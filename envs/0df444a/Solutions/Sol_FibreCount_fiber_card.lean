-- Prove2me | solution 1 for FibreCount.fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:20.225088+00:00
-- url     : https://prove2.me/submissions/d69bb840-ffdb-410d-ad0c-6c863bb7d471

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_CardFibreCompl
import Theorems.Thm_FibreCount_card_fibre_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open FibreCount
namespace FibreCount
theorem _root_.solution {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U)
    (hφ : Function.Surjective φ) {k : ℕ} (g : Fin k → U) :
    Nat.card {z : Fin k → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} =
      Fintype.card K ^ (Module.finrank K (Submodule.span K (Set.range g)) *
        Module.finrank K (LinearMap.ker φ)) *
      ∏ i ∈ Finset.range (k - Module.finrank K (Submodule.span K (Set.range g))),
        (Fintype.card K ^ Module.finrank K (LinearMap.ker φ) - Fintype.card K ^ i) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V
  induction k with
  | zero =>
    have h1 : Nat.card {z : Fin 0 → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
        ⟨⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩⟩⟩
    rw [h1, Set.range_eq_empty, Submodule.span_empty, finrank_bot]
    simp
  | succ k ih =>
    set gk : Fin k → U := fun j => g (Fin.castSucc j) with hgk
    set e := Module.finrank K (LinearMap.ker φ) with he
    set r := Module.finrank K (span K (Set.range gk)) with hr
    set q := Fintype.card K with hq
    have hstep : ∀ z' : {z' : Fin k → V // LinearIndependent K z' ∧ ∀ j, φ (z' j) = gk j},
        Nat.card {x : V // x ∉ span K (Set.range z'.1) ∧ φ x = g (Fin.last k)} =
          if g (Fin.last k) ∈ span K (Set.range gk) then q ^ e - q ^ (k - r) else q ^ e := by
      intro z'
      have h := card_fibre_compl φ hφ z'.1 z'.2.1 (g (Fin.last k))
      have hfz : (fun j => φ (z'.1 j)) = gk := funext z'.2.2
      rw [hfz] at h
      exact h
    have hequiv : {z : Fin (k + 1) → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} ≃
        Σ z' : {z' : Fin k → V // LinearIndependent K z' ∧ ∀ j, φ (z' j) = gk j},
          {x : V // x ∉ span K (Set.range z'.1) ∧ φ x = g (Fin.last k)} :=
      { toFun := fun z =>
          have hs := linearIndependent_fin_snoc.mp (by rw [Fin.snoc_init_self]; exact z.2.1)
          ⟨⟨Fin.init z.1, hs.1, fun j => z.2.2 _⟩, ⟨z.1 (Fin.last k), hs.2, z.2.2 _⟩⟩
        invFun := fun p => ⟨Fin.snoc p.1.1 p.2.1, linearIndependent_fin_snoc.mpr ⟨p.1.2.1, p.2.2.1⟩,
          fun j => by
            refine Fin.lastCases ?_ (fun i => ?_) j
            · rw [Fin.snoc_last]; exact p.2.2.2
            · rw [Fin.snoc_castSucc]; exact p.1.2.2 i⟩
        left_inv := fun z => Subtype.ext (Fin.snoc_init_self z.1)
        right_inv := fun p => by
          rcases p with ⟨⟨z', h1, h2⟩, ⟨x, h3, h4⟩⟩
          simp [Fin.init_snoc, Fin.snoc_last]
          exact (Subtype.heq_iff_coe_eq (fun y => by simp [Fin.init_snoc])).mpr rfl }
    rw [Nat.card_congr hequiv, Nat.card_sigma, Finset.sum_congr rfl (fun z' _ => hstep z'),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, ih gk]

    have hrange : Set.range g = insert (g (Fin.last k)) (Set.range gk) := by
      ext u
      simp only [Set.mem_range, Set.mem_insert_iff]
      constructor
      · rintro ⟨j, rfl⟩
        refine Fin.lastCases (Or.inl rfl) (fun i => Or.inr ⟨i, rfl⟩) j
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    have hle : r ≤ k := by
      rw [hr]
      exact (finrank_span_le_card (Set.range gk)).trans
        (by simp only [Set.toFinset_range]; exact Finset.card_image_le.trans (by simp))
    split_ifs with hmem
    · have hspan : span K (Set.range g) = span K (Set.range gk) := by
        rw [hrange, Submodule.span_insert_eq_span hmem]
      rw [hspan, ← hr, show k + 1 - r = (k - r) + 1 by omega, Finset.prod_range_succ]
      ring
    · have hspan : Module.finrank K (span K (Set.range g)) = r + 1 := by
        rw [hrange, Submodule.span_insert]
        haveI : FiniteDimensional K (span K (Set.range gk)) :=
          FiniteDimensional.span_of_finite K (Set.finite_range _)
        have hx0 : g (Fin.last k) ≠ 0 := fun h0 => hmem (h0 ▸ Submodule.zero_mem _)
        have hdis : span K {g (Fin.last k)} ⊓ span K (Set.range gk) = ⊥ := by
          rw [inf_comm, ← disjoint_iff]
          exact (Submodule.disjoint_span_singleton' hx0).mpr hmem
        have h := Submodule.finrank_sup_add_finrank_inf_eq (span K {g (Fin.last k)})
          (span K (Set.range gk))
        rw [hdis, finrank_bot, finrank_span_singleton hx0] at h
        omega
      rw [hspan, show k + 1 - (r + 1) = k - r by omega, ← hr]
      ring
end FibreCount
