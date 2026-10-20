-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.codim_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:11:59.967384+00:00
-- url     : https://prove2.me/submissions/3b1b66a0-1e87-403a-bd1b-af84598eaa71

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.codim_one
import Mathlib
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_exists_highestWeight
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_highestWeight_nat
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_highestWeight
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_ops_zero_of_trivial
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_comm_apply_E
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_comm_apply_F
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_comm_apply_H
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_apply_eq
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterDoubleSlit
open BookProof.ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2



universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}
open BookProof.ChapterWeylSl2.Sl2Rep in
theorem aux_ops_zero_min {V : Type u} [AddCommGroup V] [Module ℂ V] {R : Sl2Rep V} [FiniteDimensional ℂ V] {W : Submodule ℂ V}
    (hW : R.IsInv W) (hne : W ≠ ⊥) (hmin : ∀ U ≤ W, R.IsInv U → U = ⊥ ∨ U = W)
    (hcas : ∀ x ∈ W, R.cas x = 0) : ∀ x ∈ W, R.E x = 0 ∧ R.F x = 0 ∧ R.H x = 0 := by 
  classical
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨w, lam, hw0, hEw, hHw⟩ := BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight (R.restr W hW)
  have hE : R.E (w : V) = 0 := by
    have := congrArg Subtype.val hEw
    simpa [BookProof.ChapterWeylSl2.Sl2Rep.restr, LinearMap.restrict_coe_apply] using this
  have hH : R.H (w : V) = lam • (w : V) := by
    have := congrArg Subtype.val hHw
    simpa [BookProof.ChapterWeylSl2.Sl2Rep.restr, LinearMap.restrict_coe_apply] using this
  have hw0' : (w : V) ≠ 0 := by
    intro h; apply hw0; exact Subtype.ext h
  obtain ⟨m, hm, hF⟩ := BookProof.ChapterWeylSl2.Sl2Rep.highestWeight_nat hw0' hE hH
  have hc := BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight hE hH
  rw [hcas w w.2] at hc
  have h0 : lam ^ 2 + 2 * lam = 0 := by
    by_contra h
    exact hw0' ((smul_eq_zero.mp hc.symm).resolve_left h)
  rw [hm] at h0
  have hm0 : m = 0 := by
    have : ((m ^ 2 + 2 * m : ℕ) : ℂ) = 0 := by push_cast; exact h0
    have : m ^ 2 + 2 * m = 0 := by exact_mod_cast this
    nlinarith
  subst hm0
  have hF' : R.F (w : V) = 0 := by simpa using hF
  have hH' : R.H (w : V) = 0 := by rw [hH, hm]; simp
  set U := Submodule.span ℂ {(w : V)} with hUdef
  have hU : R.IsInv U := by
    refine ⟨?_, ?_, ?_⟩ <;>
    · intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [hE, hF', hH']
  have hUW : U ≤ W := by
    rw [hUdef, Submodule.span_le, Set.singleton_subset_iff]; exact w.2
  rcases hmin U hUW hU with h | h
  · exfalso
    have : (w : V) ∈ U := Submodule.mem_span_singleton_self _
    rw [h, Submodule.mem_bot] at this
    exact hw0' this
  · intro x hx
    rw [← h] at hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [hE, hF', hH']

theorem aux_finrank_ker {X : Type u} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (phi : X →ₗ[ℂ] ℂ) (x0 : X) (h : phi x0 = 1) :
    Module.finrank ℂ (LinearMap.ker phi) + 1 = Module.finrank ℂ X := by
  have hr : LinearMap.range phi = ⊤ :=
    LinearMap.range_eq_top.mpr fun c => ⟨c • x0, by simp [h]⟩
  have := LinearMap.finrank_range_add_finrank_ker phi
  rw [hr, finrank_top, Module.finrank_self] at this
  omega

open BookProof.ChapterWeylSl2.Sl2Rep in
theorem solution : ∀ (n : ℕ) {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (R : Sl2Rep V) (phi : V →ₗ[ℂ] ℂ) (v0 : V), phi v0 = 1 →
    (∀ v, phi (R.E v) = 0) → (∀ v, phi (R.F v) = 0) → (∀ v, phi (R.H v) = 0) →
    Module.finrank ℂ (LinearMap.ker phi) ≤ n →
    ∃ v : V, phi v = 1 ∧ R.E v = 0 ∧ R.F v = 0 ∧ R.H v = 0 := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ R phi v0 h1 hE hF hH hn
    have hK : LinearMap.ker phi = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    refine ⟨v0, h1, ?_, ?_, ?_⟩
    · have : R.E v0 ∈ LinearMap.ker phi := hE v0
      rwa [hK, Submodule.mem_bot] at this
    · have : R.F v0 ∈ LinearMap.ker phi := hF v0
      rwa [hK, Submodule.mem_bot] at this
    · have : R.H v0 ∈ LinearMap.ker phi := hH v0
      rwa [hK, Submodule.mem_bot] at this
  | succ n ih =>
    intro V _ _ _ R phi v0 h1 hE hF hH hn
    classical
    set K := LinearMap.ker phi with hKdef
    have hEK : ∀ v, R.E v ∈ K := hE
    have hFK : ∀ v, R.F v ∈ K := hF
    have hHK : ∀ v, R.H v ∈ K := hH
    have hKinv : R.IsInv K := ⟨fun x _ => hEK x, fun x _ => hFK x, fun x _ => hHK x⟩
    have hdimK := aux_finrank_ker phi v0 h1
    by_cases hsub : ∃ W : Submodule ℂ V, R.IsInv W ∧ W ≤ K ∧ W ≠ ⊥ ∧ W ≠ K
    · obtain ⟨W, hW, hWK, hW0, hWne⟩ := hsub
      -- quotient step
      let R' := R.quot W hW
      let phib : (V ⧸ W) →ₗ[ℂ] ℂ := W.liftQ phi hWK
      have hphib : ∀ v, phib (Submodule.Quotient.mk v) = phi v := fun v => rfl
      have hR'E : ∀ v, R'.E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (R.E v) :=
        fun v => rfl
      have hR'F : ∀ v, R'.F (Submodule.Quotient.mk v) = Submodule.Quotient.mk (R.F v) :=
        fun v => rfl
      have hR'H : ∀ v, R'.H (Submodule.Quotient.mk v) = Submodule.Quotient.mk (R.H v) :=
        fun v => rfl
      have hWpos : 0 < Module.finrank ℂ W := by
        rcases Nat.eq_zero_or_pos (Module.finrank ℂ W) with h | h
        · exact absurd (Submodule.finrank_eq_zero.mp h) hW0
        · exact h
      have hq : Module.finrank ℂ (V ⧸ W) + Module.finrank ℂ W = Module.finrank ℂ V :=
        Submodule.finrank_quotient_add_finrank W
      have hdimQ : Module.finrank ℂ (LinearMap.ker phib) + 1 = Module.finrank ℂ (V ⧸ W) :=
        aux_finrank_ker phib (Submodule.Quotient.mk v0) (by rw [hphib, h1])
      have hd : Module.finrank ℂ (LinearMap.ker phib) ≤ n := by
        have e1 : Module.finrank ℂ (LinearMap.ker phib) + 1 + Module.finrank ℂ W =
            Module.finrank ℂ K + 1 := by rw [hdimQ, hq, hdimK]
        omega
      obtain ⟨ub, hub1, hubE, hubF, hubH⟩ := ih (R := R') phib (Submodule.Quotient.mk v0)
        (by rw [hphib, h1])
        (fun x => Submodule.Quotient.induction_on W x fun v => by rw [hR'E, hphib, hE])
        (fun x => Submodule.Quotient.induction_on W x fun v => by rw [hR'F, hphib, hF])
        (fun x => Submodule.Quotient.induction_on W x fun v => by rw [hR'H, hphib, hH])
        hd
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective W ub
      rw [hphib] at hub1
      have huE : R.E u ∈ W := by
        rw [hR'E, Submodule.Quotient.mk_eq_zero] at hubE; exact hubE
      have huF : R.F u ∈ W := by
        rw [hR'F, Submodule.Quotient.mk_eq_zero] at hubF; exact hubF
      have huH : R.H u ∈ W := by
        rw [hR'H, Submodule.Quotient.mk_eq_zero] at hubH; exact hubH
      -- sub step
      set W' := W ⊔ Submodule.span ℂ {u} with hW'def
      have hle : W ≤ W' := le_sup_left
      have hW' : R.IsInv W' := by
        have key : ∀ (T : Module.End ℂ V), (∀ x ∈ W, T x ∈ W) → T u ∈ W →
            ∀ x ∈ W', T x ∈ W' := by
          intro T hT hTu x hx
          obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
          rw [map_add, map_smul]
          exact hle (W.add_mem (hT y hy) (W.smul_mem a hTu))
        exact ⟨key _ hW.1 huE, key _ hW.2.1 huF, key _ hW.2.2 huH⟩
      have huW' : u ∈ W' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)
      let R2 := R.restr W' hW'
      let phi2 : W' →ₗ[ℂ] ℂ := phi.comp W'.subtype
      have hdim2 := aux_finrank_ker phi2 ⟨u, huW'⟩ hub1
      have hsupd : Module.finrank ℂ W' ≤ Module.finrank ℂ W + 1 := by
        have h1' : Module.finrank ℂ W' ≤ Module.finrank ℂ W +
            Module.finrank ℂ (Submodule.span ℂ ({u} : Set V)) :=
          Submodule.finrank_add_le_finrank_add_finrank W (Submodule.span ℂ {u})
        have h2' : Module.finrank ℂ (Submodule.span ℂ ({u} : Set V)) ≤ 1 := by
          simpa using finrank_span_le_card ({u} : Set V)
        omega
      have hlt : Module.finrank ℂ W < Module.finrank ℂ K :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hWK hWne)
      obtain ⟨v, hv1, hvE, hvF, hvH⟩ := ih (R := R2) phi2 ⟨u, huW'⟩ hub1
        (fun x => hE x) (fun x => hF x) (fun x => hH x) (by omega)
      refine ⟨v, hv1, ?_, ?_, ?_⟩
      · exact congrArg Subtype.val hvE
      · exact congrArg Subtype.val hvF
      · exact congrArg Subtype.val hvH
    · push_neg at hsub
      by_cases hK0 : K = ⊥
      · refine ⟨v0, h1, ?_, ?_, ?_⟩
        · have := hEK v0; rwa [hK0, Submodule.mem_bot] at this
        · have := hFK v0; rwa [hK0, Submodule.mem_bot] at this
        · have := hHK v0; rwa [hK0, Submodule.mem_bot] at this
      have hmin : ∀ U ≤ K, R.IsInv U → U = ⊥ ∨ U = K := by
        intro U hU hUi
        by_cases h : U = ⊥
        · exact Or.inl h
        · exact Or.inr (hsub U hUi hU h)
      have hcasK : ∀ v, R.cas v ∈ K := by
        intro v
        rw [cas_apply_eq]
        exact K.add_mem (K.nsmul_mem (K.add_mem (hEK _) (hFK _)) 2) (hHK _)
      haveI : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK0
      let C : Module.End ℂ K := R.cas.restrict (fun x _ => hcasK x)
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue C
      obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
      have hxC : C x = c • x := hx.apply_eq_smul
      have hx0 : (x : V) ≠ 0 := fun h => hx.2 (Subtype.ext h)
      have hxcas : R.cas (x : V) = c • (x : V) := congrArg Subtype.val hxC
      set U := Module.End.eigenspace R.cas c ⊓ K with hUdef
      have hmemU : ∀ y, y ∈ U ↔ (R.cas y = c • y ∧ y ∈ K) := by
        intro y
        rw [hUdef, Submodule.mem_inf, Module.End.mem_eigenspace_iff]
      have hcommT : ∀ (T : Module.End ℂ V), (∀ v, R.cas (T v) = T (R.cas v)) →
          (∀ v, T v ∈ K) → ∀ y ∈ U, T y ∈ U := by
        intro T hT hTK y hy
        rw [hmemU] at hy ⊢
        refine ⟨?_, hTK y⟩
        rw [hT, hy.1, map_smul]
      have hUinv : R.IsInv U :=
        ⟨hcommT _ (cas_comm_apply_E) hEK, hcommT _ (cas_comm_apply_F) hFK,
          hcommT _ (cas_comm_apply_H) hHK⟩
      have hU0 : U ≠ ⊥ := by
        intro h
        have : (x : V) ∈ U := (hmemU _).mpr ⟨hxcas, x.2⟩
        rw [h, Submodule.mem_bot] at this
        exact hx0 this
      have hUK : U = K := (hmin U inf_le_right hUinv).resolve_left hU0
      have hcasc : ∀ y ∈ K, R.cas y = c • y := by
        intro y hy
        rw [← hUK] at hy
        exact ((hmemU y).mp hy).1
      by_cases hc0 : c = 0
      · have hz := aux_ops_zero_min hKinv hK0 hmin (fun y hy => by rw [hcasc y hy, hc0, zero_smul])
        have := ops_zero_of_trivial (W := K) (fun v => ⟨hEK v, hFK v, hHK v⟩) hz v0
        exact ⟨v0, h1, this⟩
      · set v := v0 - c⁻¹ • R.cas v0 with hvdef
        have hcv : R.cas v = 0 := by
          rw [hvdef, map_sub, map_smul, hcasc _ (hcasK v0), smul_smul, inv_mul_cancel₀ hc0,
            one_smul, sub_self]
        have hphiv : phi v = 1 := by
          have : phi (R.cas v0) = 0 := hcasK v0
          rw [hvdef, map_sub, map_smul, this, h1, smul_zero, sub_zero]
        have kill : ∀ (T : Module.End ℂ V), (∀ v, R.cas (T v) = T (R.cas v)) →
            (∀ v, T v ∈ K) → T v = 0 := by
          intro T hT hTK
          have h2 : R.cas (T v) = 0 := by rw [hT, hcv, map_zero]
          rw [hcasc _ (hTK v)] at h2
          exact (smul_eq_zero.mp h2).resolve_left hc0
        exact ⟨v, hphiv, kill _ cas_comm_apply_E hEK, kill _ cas_comm_apply_F hFK,
          kill _ cas_comm_apply_H hHK⟩
