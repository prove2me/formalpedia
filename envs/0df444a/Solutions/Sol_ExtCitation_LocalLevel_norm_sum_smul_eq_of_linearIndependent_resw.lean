-- Prove2me | solution 1 for ExtCitation.LocalLevel.norm_sum_smul_eq_of_linearIndependent_resw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/37368f92-69bb-56c0-9f12-24fff3c05b89

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_norm_sum_smul_eq_of_linearIndependent_resw

set_option autoImplicit false

open ExtCitation ExtCitation.LocalLevel
open scoped NNReal

namespace P2mS17E

variable (q : ℕ) [Fact q.Prime]
variable (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

noncomputable def intRw : ℤ_[q] →+* Rw q Kw :=
  ((algebraMap ℚ_[q] Kw).comp (PadicInt.Coe.ringHom (p := q))).codRestrict (Rw q Kw).toSubring (fun z => by
    show algebraMap Kw (PadicAlgCl q) (algebraMap ℚ_[q] Kw (z : ℚ_[q])) ∈ padicIntegers q
    rw [mem_padicIntegers_iff, ← IsScalarTower.algebraMap_apply]
    have h1 : ‖(algebraMap ℚ_[q] (PadicAlgCl q)) (z : ℚ_[q])‖ = ‖(z : ℚ_[q])‖ := PadicAlgCl.norm_extends q (z : ℚ_[q])
    have h2 : ‖(z : ℚ_[q])‖ ≤ 1 := z.2
    have : ‖(algebraMap ℚ_[q] (PadicAlgCl q)) (z : ℚ_[q])‖₊ ≤ 1 := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, h1]; exact h2
    exact this)

theorem coe_coe_intRw (z : ℤ_[q]) :
    (((intRw q Kw z : Rw q Kw) : Kw) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) (z : ℚ_[q]) := by
  show algebraMap Kw (PadicAlgCl q) (algebraMap ℚ_[q] Kw (z : ℚ_[q])) = _
  rw [← IsScalarTower.algebraMap_apply]

theorem coe_intRw (z : ℤ_[q]) : ((intRw q Kw z : Rw q Kw) : Kw) = algebraMap ℚ_[q] Kw (z : ℚ_[q]) := rfl

theorem algebraMap_intRw (z : ℤ_[q]) : algebraMap (Rw q Kw) (OO q) (intRw q Kw z) = algebraMap ℤ_[q] (OO q) z := by
  apply Subtype.ext
  rw [algebraMap_Rw_coe, coe_coe_intRw, algebraMap_OO_coe]

theorem resw_intRw (z : ℤ_[q]) : resw q Kw (intRw q Kw z) = algebraMap (ZMod q) (kbar q) (PadicInt.toZMod z) := by
  rw [resw_def, algebraMap_intRw, algebraMap_toZMod]

theorem norm_eq_one_of_resw_ne_zero (x : Rw q Kw) (hx : resw q Kw x ≠ 0) : ‖((x : Kw) : PadicAlgCl q)‖ = 1 := by
  have hX : algebraMap (Rw q Kw) (OO q) x ∉ IsLocalRing.maximalIdeal (OO q) := by
    rwa [Ne, resw_def, IsLocalRing.residue_eq_zero_iff] at hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hX
  obtain ⟨u, hu⟩ := hX
  have hle : ∀ y : OO q, ‖(y : PadicAlgCl q)‖ ≤ 1 := fun y => by
    have := y.2; rw [mem_padicIntegers_iff] at this; exact_mod_cast this
  have h1 := hle (u : OO q)
  have h2 := hle (↑u⁻¹ : OO q)
  have h3 : ‖((u : OO q) : PadicAlgCl q)‖ * ‖((↑u⁻¹ : OO q) : PadicAlgCl q)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv, OneMemClass.coe_one, norm_one]
  have h4 : ‖((u : OO q) : PadicAlgCl q)‖ = 1 := by
    nlinarith [norm_nonneg ((u : OO q) : PadicAlgCl q), norm_nonneg ((↑u⁻¹ : OO q) : PadicAlgCl q)]
  rw [← algebraMap_Rw_coe, ← hu]
  exact h4

theorem main {ι : Type} [Fintype ι] (y : ι → Rw q Kw) (hy : LinearIndependent (ZMod q) (fun i => resw q Kw (y i)))
    (c : ι → ℚ_[q]) (j : ι) (hj : ∀ i, ‖c i‖ ≤ ‖c j‖) :
    ‖((∑ i, c i • ((y i : Kw)) : Kw) : PadicAlgCl q)‖ = ‖c j‖ := by
  classical
  by_cases hcj : c j = 0
  ·
    have hc : ∀ i, c i = 0 := fun i => norm_le_zero_iff.mp ((hj i).trans (by rw [hcj, norm_zero]))
    simp [hc]

  have hd : ∀ i, ‖c i / c j‖ ≤ 1 := fun i => by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hcj)]; exact hj i
  let d : ι → ℤ_[q] := fun i => ⟨c i / c j, hd i⟩
  have hdj : d j = 1 := Subtype.ext (div_self hcj)

  let T : Rw q Kw := ∑ i, intRw q Kw (d i) * y i
  let e₁ : Rw q Kw →+* Kw := (Rw q Kw).subtype
  let e₂ : Kw →+* PadicAlgCl q := algebraMap Kw (PadicAlgCl q)
  have he : ∀ z : ℤ_[q], e₂ (e₁ (intRw q Kw z)) = algebraMap ℚ_[q] (PadicAlgCl q) (z : ℚ_[q]) := fun z =>
    coe_coe_intRw q Kw z

  have hres : resw q Kw T ≠ 0 := by
    intro h0
    have hsum : ∑ i, (PadicInt.toZMod (d i)) • resw q Kw (y i) = 0 := by
      have : resw q Kw T = ∑ i, resw q Kw (intRw q Kw (d i)) * resw q Kw (y i) := by
        simp only [T, resw_def, map_sum, map_mul]
      rw [this] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [resw_intRw, Algebra.smul_def]
    have hall := (Fintype.linearIndependent_iff.mp hy) (fun i => PadicInt.toZMod (d i)) hsum j
    simp only [hdj, map_one] at hall
    exact one_ne_zero hall

  have hT1 : ‖e₂ (e₁ T)‖ = 1 := norm_eq_one_of_resw_ne_zero q Kw T hres

  have hTsum : e₂ (e₁ T) = ∑ i, algebraMap ℚ_[q] (PadicAlgCl q) (c i / c j) * e₂ (e₁ (y i)) := by
    simp only [T, map_sum, map_mul, he]
    rfl
  have hS : e₂ (∑ i, c i • (y i : Kw)) = algebraMap ℚ_[q] (PadicAlgCl q) (c j) * e₂ (e₁ T) := by
    rw [hTsum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← mul_assoc, ← map_mul, mul_div_cancel₀ _ hcj]
    rfl
  change ‖e₂ (∑ i, c i • (y i : Kw))‖ = ‖c j‖
  rw [hS, norm_mul, hT1, mul_one]
  exact PadicAlgCl.norm_extends q (c j)

end P2mS17E

open ExtCitation ExtCitation.LocalLevel in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    {ι : Type} [Fintype ι] (y : ι → Rw q Kw) (hy : LinearIndependent (ZMod q) (fun i => resw q Kw (y i)))
    (c : ι → ℚ_[q]) (j : ι) (hj : ∀ i, ‖c i‖ ≤ ‖c j‖) :
    ‖((∑ i, c i • ((y i : Kw)) : Kw) : PadicAlgCl q)‖ = ‖c j‖ :=
  P2mS17E.main q Kw y hy c j hj

end S_ExtCitation_LocalLevel_norm_sum_smul_eq_of_linearIndependent_resw
end P2MW
export P2MW.S_ExtCitation_LocalLevel_norm_sum_smul_eq_of_linearIndependent_resw (solution)
