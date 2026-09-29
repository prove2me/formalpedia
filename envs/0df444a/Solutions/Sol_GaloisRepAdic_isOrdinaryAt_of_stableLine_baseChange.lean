-- Prove2me | solution 1 for GaloisRepAdic.isOrdinaryAt_of_stableLine_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/575a21a6-bc3d-5edb-b9d2-3909a7a91d79

import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isOrdinaryAt_of_stableLine_baseChange

open Polynomial TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace OrdPtSat

section Sat

variable {A : Type} [CommRing A] [IsDomain A]
variable {V : Type} [AddCommGroup V] [Module A V]

def sat (N : Submodule A V) : Submodule A V where
  carrier := {v | ∃ a : A, a ≠ 0 ∧ a • v ∈ N}
  add_mem' := by
    rintro x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem b hax
    · rw [mul_smul]; exact N.smul_mem a hby
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c x ⟨a, ha, hax⟩
    exact ⟨a, ha, by rw [smul_comm]; exact N.smul_mem c hax⟩

theorem mem_sat {N : Submodule A V} {v : V} :
    v ∈ sat N ↔ ∃ a : A, a ≠ 0 ∧ a • v ∈ N := Iff.rfl

theorem le_sat (N : Submodule A V) : N ≤ sat N :=
  fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩

theorem sat_ne_bot {N : Submodule A V} (hN : N ≠ ⊥) : sat N ≠ ⊥ := by
  intro h
  exact hN (le_bot_iff.mp (h ▸ le_sat N))

theorem sat_saturated {N : Submodule A V} {a : A} {v : V} (ha : a ≠ 0)
    (hav : a • v ∈ sat N) : v ∈ sat N := by
  obtain ⟨b, hb, hbav⟩ := hav
  exact ⟨b * a, mul_ne_zero hb ha, by rwa [mul_smul]⟩

theorem sat_stable {N : Submodule A V} (T : V →ₗ[A] V)
    (hT : ∀ v ∈ N, T v ∈ N) : ∀ v ∈ sat N, T v ∈ sat N := by
  rintro v ⟨a, ha, hav⟩
  exact ⟨a, ha, by rw [← map_smul]; exact hT _ hav⟩

theorem sat_pairDep {N : Submodule A V}
    (hdep : ∀ x ∈ N, ∀ y ∈ N, ∃ c d : A, ¬(c = 0 ∧ d = 0) ∧ c • x + d • y = 0) :
    ∀ x ∈ sat N, ∀ y ∈ sat N,
      ∃ c d : A, ¬(c = 0 ∧ d = 0) ∧ c • x + d • y = 0 := by
  rintro x ⟨a, ha, hax⟩ y ⟨b, hb, hby⟩
  obtain ⟨c, d, hcd, hrel⟩ := hdep _ hax _ hby
  refine ⟨c * a, d * b, ?_, ?_⟩
  · rintro ⟨hca, hdb⟩
    refine hcd ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp hca with h | h
      · exact h
      · exact absurd h ha
    · rcases mul_eq_zero.mp hdb with h | h
      · exact h
      · exact absurd h hb
  · rw [mul_smul, mul_smul]
    exact hrel

end Sat

section Engine

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {V : Type} [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]

theorem exists_basis_span_of_saturated (hrk : Module.finrank A V = 2)
    (L : Submodule A V) (hL0 : L ≠ ⊥)
    (hdep : ∀ x ∈ L, ∀ y ∈ L, ∃ c d : A, ¬(c = 0 ∧ d = 0) ∧ c • x + d • y = 0)
    (hsat : ∀ (a : A) (v : V), a ≠ 0 → a • v ∈ L → v ∈ L) :
    ∃ b : Module.Basis (Fin 2) A V, L = A ∙ b 0 := by
  classical
  obtain ⟨n, snf⟩ := L.smithNormalForm (Module.finBasisOfFinrankEq A V hrk)
  obtain ⟨bM, bN, f, a, hsnf⟩ := snf
  have hn1 : 1 ≤ n := by
    by_contra hn
    push Not at hn
    interval_cases n
    apply hL0
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hrepr := bN.sum_repr ⟨x, hx⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hrepr
    exact congrArg Subtype.val hrepr.symm
  have hn2 : n ≤ 1 := by
    by_contra hn
    push Not at hn
    have h0n : (0 : ℕ) < n := by omega
    have h1n : (1 : ℕ) < n := hn
    set i0 : Fin n := ⟨0, h0n⟩ with hi0
    set i1 : Fin n := ⟨1, h1n⟩ with hi1
    have hne : i1 ≠ i0 := by
      simp [hi0, hi1, Fin.ext_iff]
    obtain ⟨c, d, hcd, hrel⟩ :=
      hdep (bN i0 : V) (bN i0).2 (bN i1 : V) (bN i1).2
    have hrelL : c • bN i0 + d • bN i1 = (0 : ↥L) := by
      apply Subtype.ext
      simpa using hrel
    have hfs := congrArg (fun z => bN.repr z) hrelL
    simp only [map_add, map_smul, Module.Basis.repr_self, map_zero] at hfs
    have hc : c = 0 := by
      have h2 := DFunLike.congr_fun hfs i0
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (Ne.symm hne), smul_eq_mul, mul_one, mul_zero, add_zero,
        Finsupp.coe_zero, Pi.zero_apply] at h2
      exact h2
    have hd : d = 0 := by
      have h2 := DFunLike.congr_fun hfs i1
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hne, smul_eq_mul, mul_one, mul_zero, zero_add,
        Finsupp.coe_zero, Pi.zero_apply] at h2
      exact h2
    exact hcd ⟨hc, hd⟩
  have hn : n = 1 := le_antisymm hn2 hn1
  subst hn
  have ha0 : a 0 ≠ 0 := by
    intro h0
    have hz : (bN 0 : V) = 0 := by rw [hsnf 0, h0, zero_smul]
    exact bN.ne_zero 0 (Subtype.ext hz)
  have hgen : bM (f 0) ∈ L := by
    refine hsat (a 0) (bM (f 0)) ha0 ?_
    rw [← hsnf 0]
    exact (bN 0).2
  have hspan : L = A ∙ bM (f 0) := by
    apply le_antisymm
    · intro x hx
      have hrepr := bN.sum_repr ⟨x, hx⟩
      rw [Fin.sum_univ_one] at hrepr
      have hcoe : (bN.repr ⟨x, hx⟩) 0 • ((bN 0 : ↥L) : V) = x := by
        have := congrArg Subtype.val hrepr
        simpa using this
      have hx2 : x = (bN.repr ⟨x, hx⟩ 0 * a 0) • bM (f 0) := by
        rw [mul_smul, ← hsnf 0]
        exact hcoe.symm
      rw [hx2]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hgen
  refine ⟨bM.reindex (Equiv.swap (f 0) 0), ?_⟩
  rw [hspan]
  congr 1
  rw [Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right]

end Engine

section Psi

theorem one_tmul_injective {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B))
    {V : Type} [AddCommGroup V] [Module A V] [Module.Free A V] :
    Function.Injective (fun v : V => (1 : B) ⊗ₜ[A] v) := by
  have h1 : Function.Injective ((Algebra.linearMap A B).rTensor V) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := V) _ hinj
  intro x y hxy
  have h2 : ((Algebra.linearMap A B).rTensor V) ((TensorProduct.lid A V).symm x) =
      ((Algebra.linearMap A B).rTensor V) ((TensorProduct.lid A V).symm y) := by
    simpa [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
      Algebra.linearMap_apply, map_one] using hxy
  exact (TensorProduct.lid A V).symm.injective (h1 h2)

end Psi

section Coords

variable {A : Type} [CommRing A] [IsDomain A]
variable {V : Type} [AddCommGroup V] [Module A V]

omit [IsDomain A] in

theorem coeff_eq_of_combo_eq {B : Type} [CommRing B] [Algebra A B]
    (e : Module.Basis (Fin 2) A V) (c0 c1 d0 d1 : B)
    (h : c0 • ((e.baseChange B) 0) + c1 • ((e.baseChange B) 1)
       = d0 • ((e.baseChange B) 0) + d1 • ((e.baseChange B) 1)) :
    c0 = d0 ∧ c1 = d1 := by
  have hfs := congrArg (fun z => (e.baseChange B).repr z) h
  simp only [map_add, map_smul, Module.Basis.repr_self] at hfs
  constructor
  · have h2 := DFunLike.congr_fun hfs (0 : Fin 2)
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul, mul_one,
      mul_zero, add_zero] at h2
    exact h2
  · have h2 := DFunLike.congr_fun hfs (1 : Fin 2)
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_one,
      mul_zero, zero_add] at h2
    exact h2

theorem pair_dep_of_det_eq_zero (e : Module.Basis (Fin 2) A V) (x y : V)
    (hdet : e.repr x 0 * e.repr y 1 - e.repr x 1 * e.repr y 0 = 0) :
    ∃ c d : A, ¬(c = 0 ∧ d = 0) ∧ c • x + d • y = 0 := by
  have hx := e.sum_repr x
  have hy := e.sum_repr y
  rw [Fin.sum_univ_two] at hx hy
  set x0 := e.repr x 0 with hx0def
  set x1 := e.repr x 1 with hx1def
  set y0 := e.repr y 0 with hy0def
  set y1 := e.repr y 1 with hy1def
  by_cases h0 : x0 = 0
  · by_cases h1 : x1 = 0
    · refine ⟨1, 0, by simp, ?_⟩
      have hxz : x = 0 := by rw [← hx, h0, h1, zero_smul, zero_smul, add_zero]
      rw [hxz]; simp
    · have hy0 : y0 = 0 := by
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at hdet
        rcases mul_eq_zero.mp hdet with h | h
        · exact absurd h h1
        · exact h
      refine ⟨-y1, x1, fun hc => h1 hc.2, ?_⟩
      rw [← hx, ← hy]
      match_scalars
      · linear_combination (-y1) * h0 + x1 * hy0
      · ring
  · refine ⟨-y0, x0, fun hc => h0 hc.2, ?_⟩
    rw [← hx, ← hy]
    match_scalars
    · ring
    · linear_combination hdet

end Coords

end OrdPtSat

theorem solution
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
    (ρ : GaloisRepAdic A) (p : ℕ)
    (h : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ L : Submodule K (K ⊗[A] ρ.V),
        Module.finrank K L = 1 ∧
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ w ∈ L, (ρ.ρ σ).baseChange K w ∈ L) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : K ⊗[A] ρ.V, (ρ.ρ σ).baseChange K w - w ∈ L)) :
    ρ.IsOrdinaryAt p := by
  classical
  intro P hP
  obtain ⟨LK, hLK1, hLKD, hLKI⟩ := h P hP
  set ψ : ρ.V →ₗ[A] K ⊗[A] ρ.V := (TensorProduct.mk A K ρ.V) 1 with hψdef
  have hψ : ∀ v : ρ.V, ψ v = (1 : K) ⊗ₜ[A] v := fun v => rfl
  have hψinj : Function.Injective ψ := by
    have h1 := OrdPtSat.one_tmul_injective (A := A) (B := K)
      (IsFractionRing.injective A K) (V := ρ.V)
    intro u v huv
    exact h1 (by simpa [hψ] using huv)
  have hψsmul : ∀ (a : A) (z : K ⊗[A] ρ.V), a • z = algebraMap A K a • z := fun a z =>
    (algebraMap_smul K a z).symm
  have hamne : ∀ {a : A}, a ≠ 0 → algebraMap A K a ≠ 0 := by
    intro a ha
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha
  set N : Submodule A ρ.V := (LK.restrictScalars A).comap ψ with hNdef
  have hmemN : ∀ v : ρ.V, v ∈ N ↔ ψ v ∈ LK := fun v => Iff.rfl

  have hLKne : LK ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hLK1
    norm_num at hLK1
  obtain ⟨w, hwLK, hw0⟩ := (Submodule.ne_bot_iff LK).mp hLKne
  have hclear : ∀ z : K ⊗[A] ρ.V, ∃ a : A, a ≠ 0 ∧ ∃ v : ρ.V, ψ v = a • z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul k v =>
      obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors A) k
      refine ⟨(s : A), nonZeroDivisors.coe_ne_zero s, x • v, ?_⟩
      have h1 : ψ (x • v) = algebraMap A K x • ((1 : K) ⊗ₜ[A] v) := by
        rw [hψ, TensorProduct.tmul_smul, hψsmul]
      have h2 : (s : A) • (k ⊗ₜ[A] v) = (algebraMap A K (s : A) * k) • ((1 : K) ⊗ₜ[A] v) := by
        rw [hψsmul, ← smul_smul]
        congr 1
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, h2, ← hxs, mul_comm]
    | add z₁ z₂ ih₁ ih₂ =>
      obtain ⟨a₁, ha₁, v₁, hv₁⟩ := ih₁
      obtain ⟨a₂, ha₂, v₂, hv₂⟩ := ih₂
      refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, a₂ • v₁ + a₁ • v₂, ?_⟩
      rw [map_add, map_smul, map_smul, hv₁, hv₂, smul_add, smul_smul, smul_smul,
        mul_comm a₂ a₁]
  have hN0 : N ≠ ⊥ := by
    obtain ⟨a, ha, v, hv⟩ := hclear w
    rw [Submodule.ne_bot_iff]
    refine ⟨v, ?_, ?_⟩
    · rw [hmemN, hv, hψsmul]
      exact LK.smul_mem _ hwLK
    · intro h0
      rw [h0, map_zero] at hv
      have hz : algebraMap A K a • w = 0 := by rw [← hψsmul, ← hv]
      rcases smul_eq_zero.mp hz with h | h
      · exact hamne ha h
      · exact hw0 h

  have hNsat : ∀ (a : A) (v : ρ.V), a ≠ 0 → a • v ∈ N → v ∈ N := by
    intro a v ha hav
    rw [hmemN] at hav ⊢
    rw [map_smul, hψsmul] at hav
    have h2 := LK.smul_mem (algebraMap A K a)⁻¹ hav
    rwa [smul_smul, inv_mul_cancel₀ (hamne ha), one_smul] at h2

  have hNdep : ∀ x ∈ N, ∀ y ∈ N,
      ∃ c d : A, ¬(c = 0 ∧ d = 0) ∧ c • x + d • y = 0 := by
    intro x hx y hy
    rw [hmemN] at hx hy
    haveI : Module.Free K ↥LK := Module.Free.of_divisionRing K ↥LK
    obtain ⟨g, hg0, hgen⟩ := (finrank_eq_one_iff' (K := K) (V := ↥LK)).mp hLK1
    obtain ⟨cx, hcx⟩ := hgen ⟨ψ x, hx⟩
    obtain ⟨cy, hcy⟩ := hgen ⟨ψ y, hy⟩
    by_cases hc0 : cx = 0 ∧ cy = 0
    · have hx0 : (⟨ψ x, hx⟩ : ↥LK) = 0 := by rw [← hcx, hc0.1, zero_smul]
      have hxz : x = 0 := by
        apply hψinj
        have := congrArg Subtype.val hx0
        simpa using this
      exact ⟨1, 0, by simp, by simp [hxz]⟩
    · have hKrel : cy • ψ x - cx • ψ y = 0 := by
        have h1 : cy • (⟨ψ x, hx⟩ : ↥LK) - cx • ⟨ψ y, hy⟩ = 0 := by
          rw [← hcx, ← hcy, smul_smul, smul_smul, mul_comm cy cx]
          exact sub_self ((cx * cy) • g)
        have := congrArg Subtype.val h1
        simpa using this
      obtain ⟨⟨nx, sx⟩, hnx⟩ := IsLocalization.surj (nonZeroDivisors A) cy
      obtain ⟨⟨ny, sy⟩, hny⟩ := IsLocalization.surj (nonZeroDivisors A) cx

      refine ⟨(sy : A) * nx, -((sx : A) * ny), ?_, ?_⟩
      · rintro ⟨h1, h2⟩
        rw [neg_eq_zero] at h2
        rcases not_and_or.mp hc0 with hcx0 | hcy0
        ·
          have hny0 : ny ≠ 0 := by
            intro hz
            rw [hz, map_zero] at hny
            rcases mul_eq_zero.mp hny with h | h
            · exact hcx0 h
            · exact hamne (nonZeroDivisors.coe_ne_zero sy) h
          exact mul_ne_zero (nonZeroDivisors.coe_ne_zero sx) hny0 h2
        · have hnx0 : nx ≠ 0 := by
            intro hz
            rw [hz, map_zero] at hnx
            rcases mul_eq_zero.mp hnx with h | h
            · exact hcy0 h
            · exact hamne (nonZeroDivisors.coe_ne_zero sx) h
          exact mul_ne_zero (nonZeroDivisors.coe_ne_zero sy) hnx0 h1
      · apply hψinj
        rw [map_zero, map_add, map_smul, map_smul, hψsmul, hψsmul]
        have e1 : algebraMap A K ((sy : A) * nx) • ψ x
            = algebraMap A K ((sx : A) * (sy : A)) • (cy • ψ x) := by
          rw [smul_smul, map_mul, map_mul]
          congr 1
          rw [← hnx]; ring
        have e2 : algebraMap A K (-((sx : A) * ny)) • ψ y
            = algebraMap A K ((sx : A) * (sy : A)) • (-(cx • ψ y)) := by
          rw [smul_neg, smul_smul, map_neg,
            show -(algebraMap A K) (↑sx * ny) • ψ y = -((algebraMap A K) (↑sx * ny) • ψ y) from
              neg_smul (R := K) (M := K ⊗[A] ρ.V) _ _,
            map_mul, map_mul]
          congr 2
          rw [← hny]; ring
        rw [e1, e2, ← smul_add, ← sub_eq_add_neg, hKrel, smul_zero]
  obtain ⟨b, hb⟩ :=
    OrdPtSat.exists_basis_span_of_saturated ρ.finrank_eq N hN0 hNdep hNsat
  refine ⟨N, ⟨b, hb⟩, ?_, ?_⟩
  · intro σ hσ v hv
    rw [hmemN] at hv ⊢
    have hbc : ψ (ρ.ρ σ v) = (ρ.ρ σ).baseChange K (ψ v) := by
      rw [hψ, hψ, LinearMap.baseChange_tmul]
    rw [hbc]
    exact hLKD σ hσ _ hv
  · intro σ hσ v
    rw [hmemN]
    have hbc : ψ (ρ.ρ σ v - v) = (ρ.ρ σ).baseChange K (ψ v) - ψ v := by
      rw [map_sub]
      congr 1
    rw [hbc]
    exact hLKI σ hσ (ψ v)

end S_GaloisRepAdic_isOrdinaryAt_of_stableLine_baseChange
end P2MW
export P2MW.S_GaloisRepAdic_isOrdinaryAt_of_stableLine_baseChange (solution)
