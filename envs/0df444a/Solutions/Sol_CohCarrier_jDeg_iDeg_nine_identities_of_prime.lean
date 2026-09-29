-- Prove2me | solution 1 for CohCarrier.jDeg_iDeg_nine_identities_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c393fdc5-f8c5-587c-99ba-88554c947da3

import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_CohCarrier_jDeg_comp_iDegP_self
import Theorems.Thm_CohCarrier_index_range_iotaDeg_of_prime_sq
import Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT
import Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower
import Theorems.Thm_CohCarrier_heckeSym_top
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_dvd
import Theorems.Thm_CohCarrier_jDeg_iDeg_corner_of_prime_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDeg_iDeg_nine_identities_of_prime

set_option autoImplicit false

namespace Sol2Aux

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

private theorem entry01 {M M' : ℕ} (d : ℕ) [NeZero d]
    (h : LevelLE M M' (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod M')ˣ) d)
    (γ' : ↥(GammaH M' ⊤)) :
    ((iotaDeg M M' ⊤ ⊤ d h γ' : ↥(GammaH M ⊤)) : SL(2, ℤ)) 0 1
      = (γ' : SL(2, ℤ)) 0 1 * d := by
  show (conjLowerMat d (γ' : SL(2, ℤ)) (h.dvd_entry γ')) 0 1 = _
  simp [conjLowerMat]

private theorem entry10 {M M' : ℕ} (d : ℕ) [NeZero d]
    (h : LevelLE M M' (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod M')ˣ) d)
    (γ' : ↥(GammaH M' ⊤)) :
    ((iotaDeg M M' ⊤ ⊤ d h γ' : ↥(GammaH M ⊤)) : SL(2, ℤ)) 1 0
      = (γ' : SL(2, ℤ)) 1 0 / d := by
  show (conjLowerMat d (γ' : SL(2, ℤ)) (h.dvd_entry γ')) 1 0 = _
  simp [conjLowerMat]

private theorem entry_dvd {M' : ℕ} (γ' : ↥(GammaH M' ⊤)) :
    ((M' : ℕ) : ℤ) ∣ (γ' : SL(2, ℤ)) 1 0 := by
  obtain ⟨hA, -⟩ := mem_GammaH_iff.mp γ'.2
  rw [Gamma0_mem] at hA
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hA

variable (N q : ℕ) [NeZero N] [NeZero q]

private theorem levelLE_N_Nq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) ⊤ 1 :=
  ⟨dvd_mul_right N q, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

private theorem levelLE_Nq_Nq2_1 : LevelLE (N * q) (N * q ^ 2) (⊤ : Subgroup (ZMod (N * q))ˣ) ⊤ 1 :=
  ⟨⟨q, by ring⟩, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

private theorem levelLE_Nq_Nq2_q : LevelLE (N * q) (N * q ^ 2) (⊤ : Subgroup (ZMod (N * q))ˣ) ⊤ q := by
  refine ⟨⟨q, by ring⟩, ?_, fun _ _ => Subgroup.mem_top _⟩
  have hpos : 0 < N * q := Nat.pos_of_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne q))
  have hdiv : (N * q ^ 2) / (N * q) = q := by
    rw [show N * q ^ 2 = (N * q) * q by ring]
    exact Nat.mul_div_cancel_left q hpos
  rw [hdiv]

private theorem hom_comp (d : ℕ) [NeZero d]
    (hin : LevelLE (N * q) (N * q ^ 2) (⊤ : Subgroup (ZMod (N * q))ˣ) ⊤ d)
    (h₁₃ : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) ⊤ d) :
    iotaDeg N (N * q ^ 2) ⊤ ⊤ d h₁₃
      = (iotaDeg N (N * q) ⊤ ⊤ 1 (levelLE_N_Nq N q)).comp
          (iotaDeg (N * q) (N * q ^ 2) ⊤ ⊤ d hin) := by
  refine MonoidHom.ext fun γ' => ?_
  apply Subtype.ext
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [iotaDeg, conjLowerMat, Matrix.of_apply, mul_one, Int.ediv_one]

private theorem range_outer_eq_lower :
    (iotaDeg N (N * q) ⊤ ⊤ 1 (levelLE_N_Nq N q)).range = GammaHLower N ⊤ q := by
  apply le_antisymm
  · rintro x ⟨γ', rfl⟩
    rw [Subgroup.mem_subgroupOf, Gamma0_mem, entry10 1 (levelLE_N_Nq N q) γ',
      Nat.cast_one, Int.ediv_one, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans ⟨1, by push_cast; ring⟩ (entry_dvd γ')
  · intro g hg
    rw [Subgroup.mem_subgroupOf, Gamma0_mem] at hg
    have hc : ((q * N : ℕ) : ℤ) ∣ ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hg)
    refine ⟨⟨(g : ↥(GammaH N ⊤)), ?_⟩, ?_⟩
    · rw [GammaH_top, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact dvd_trans ⟨1, by push_cast; ring⟩ hc
    · apply Subtype.ext
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [iotaDeg, conjLowerMat, Matrix.of_apply, mul_one, Int.ediv_one]

private theorem range_inner_q_eq_upper :
    (iotaDeg (N * q) (N * q ^ 2) ⊤ ⊤ q (levelLE_Nq_Nq2_q N q)).range
      = GammaHUpper (N * q) ⊤ q := by
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  apply le_antisymm
  · rintro x ⟨γ', rfl⟩
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper,
      entry01 q (levelLE_Nq_Nq2_q N q) γ']
    push_cast
    rw [ZMod.natCast_self q]
    ring
  · intro g hg
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper] at hg
    have hb : (q : ℤ) ∣ ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 0 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hg)
    have hc : ((N * q : ℕ) : ℤ) ∣ ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0 :=
      entry_dvd g
    refine ⟨⟨⟨!![((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 0 0,
          ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 0 1 / q;
          ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0 * q,
          ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 1], ?_⟩, ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      have hdet := Matrix.SpecialLinearGroup.det_coe ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ))
      rw [Matrix.det_fin_two] at hdet
      have hbc : ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 0 1 / q
            * (((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0 * q)
          = ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 0 1
              * ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0 := by
        rw [mul_comm (((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0) (q : ℤ), ← mul_assoc,
          Int.ediv_mul_cancel hb]
      rw [hbc]
      exact hdet
    · rw [GammaH_top]
      refine Gamma0_mem.mpr ?_
      show ((((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0 * q : ℤ) : ZMod (N * q ^ 2)) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd,
        show ((N * q ^ 2 : ℕ) : ℤ) = ((N * q : ℕ) : ℤ) * q by push_cast; ring]
      exact mul_dvd_mul hc dvd_rfl
    · have hdiv01 : ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 0 1 / q * q
          = ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 0 1 := Int.ediv_mul_cancel hb
      have hdiv10 : ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0 * q / q
          = ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0 := Int.mul_ediv_cancel _ hq0
      apply Subtype.ext
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [iotaDeg, conjLowerMat, Matrix.of_apply, hdiv01, hdiv10]

private theorem lower_relindex_transport (d : ℕ) [NeZero d]
    (hin : LevelLE (N * q) (N * q ^ 2) (⊤ : Subgroup (ZMod (N * q))ˣ) ⊤ d)
    (h₁₃ : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) ⊤ d) :
    ((iotaDeg N (N * q ^ 2) ⊤ ⊤ d h₁₃).range.subgroupOf (GammaHLower N ⊤ q)).index
      = (iotaDeg (N * q) (N * q ^ 2) ⊤ ⊤ d hin).range.index := by
  show ((iotaDeg N (N * q ^ 2) ⊤ ⊤ d h₁₃).range.relIndex (GammaHLower N ⊤ q)) = _
  rw [hom_comp N q d hin h₁₃, MonoidHom.range_comp, ← range_outer_eq_lower N q,
    MonoidHom.range_eq_map (iotaDeg N (N * q) ⊤ ⊤ 1 (levelLE_N_Nq N q)),
    Subgroup.relIndex_map_map_of_injective _ _
      (iotaDeg_injective N (N * q) ⊤ ⊤ 1 (levelLE_N_Nq N q)),
    Subgroup.relIndex_top_right]

private theorem lower_relindex_q
    (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q) :
    ((iotaDeg N (N * q ^ 2) ⊤ ⊤ q hq').range.subgroupOf (GammaHLower N ⊤ q)).index = q := by
  rw [lower_relindex_transport N q q (levelLE_Nq_Nq2_q N q) hq',
    range_inner_q_eq_upper N q]
  exact index_GammaHUpper_of_dvd (N * q) ⊤ q (dvd_mul_left q N)

section LowerCount

variable {Mc : ℕ} (qc : ℕ)

private def lMat (t : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; t, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] private theorem lMat_00 (t : ℤ) : (lMat t) 0 0 = 1 := rfl
@[scoped simp] private theorem lMat_01 (t : ℤ) : (lMat t) 0 1 = 0 := rfl
@[scoped simp] private theorem lMat_10 (t : ℤ) : (lMat t) 1 0 = t := rfl
@[scoped simp] private theorem lMat_11 (t : ℤ) : (lMat t) 1 1 = 1 := rfl

private theorem mul_inv_apply_10 (x y : SL(2, ℤ)) :
    (x * y⁻¹) 1 0 = x 1 0 * y 1 1 - x 1 1 * y 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

variable (Mc) in
private theorem lMat_mem (j : ℤ) : lMat (j * Mc) ∈ GammaH Mc (⊤ : Subgroup (ZMod Mc)ˣ) := by
  have h0 : lMat (j * Mc) ∈ Gamma0 Mc := by
    rw [Gamma0_mem]
    show ((j * Mc : ℤ) : ZMod Mc) = 0
    push_cast
    rw [ZMod.natCast_self]
    ring
  exact mem_GammaH_iff.mpr ⟨h0, Subgroup.mem_top _⟩

variable (Mc) in
private def lElt (j : ℤ) : ↥(GammaH Mc (⊤ : Subgroup (ZMod Mc)ˣ)) :=
  ⟨lMat (j * Mc), lMat_mem Mc j⟩

@[scoped simp] private theorem lElt_coe (j : ℤ) :
    ((lElt Mc j : ↥(GammaH Mc (⊤ : Subgroup (ZMod Mc)ˣ))) : SL(2, ℤ)) = lMat (j * Mc) := rfl

private theorem mk_eq_mk_iff_lower (x y : ↥(GammaH Mc (⊤ : Subgroup (ZMod Mc)ˣ))) :
    (Quotient.mk'' x :
        Quotient (QuotientGroup.rightRel (GammaHLower Mc (⊤ : Subgroup (ZMod Mc)ˣ) qc)))
      = Quotient.mk'' y ↔
      ((((y : SL(2, ℤ)) * (x : SL(2, ℤ))⁻¹) 1 0 : ℤ) : ZMod (qc * Mc)) = 0 := by
  rw [Quotient.eq'', QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, Gamma0_mem,
    Subgroup.coe_mul, Subgroup.coe_inv]

private theorem natCard_rightQuot_lower [NeZero Mc] [NeZero qc] (hqM : qc ∣ Mc) :
    Nat.card (Quotient (QuotientGroup.rightRel
      (GammaHLower Mc (⊤ : Subgroup (ZMod Mc)ˣ) qc))) = qc := by
  have hM0 : (Mc : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Mc)
  have hMq : ((Mc : ℕ) : ZMod qc) = 0 := by
    obtain ⟨e, he⟩ := hqM
    rw [he]
    push_cast
    rw [ZMod.natCast_self]
    ring
  let ψ : ZMod qc → Quotient (QuotientGroup.rightRel
      (GammaHLower Mc (⊤ : Subgroup (ZMod Mc)ˣ) qc)) :=
    fun j => Quotient.mk'' (lElt Mc (j.val : ℤ))
  have hinj : Function.Injective ψ := by
    intro j j' h
    rw [mk_eq_mk_iff_lower, mul_inv_apply_10] at h
    simp only [lElt_coe, lMat_10, lMat_11] at h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have h2 : (qc : ℤ) ∣ ((j'.val : ℤ) - (j.val : ℤ)) := by
      obtain ⟨c, hc⟩ := h
      refine ⟨c, mul_right_cancel₀ hM0 ?_⟩
      push_cast at hc ⊢
      linear_combination hc
    have h3 : ((j'.val : ℤ) : ZMod qc) = ((j.val : ℤ) : ZMod qc) := by
      rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h2
    push_cast at h3
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h3
    exact h3.symm
  have hsurj : Function.Surjective ψ := by
    intro x
    induction x using Quotient.inductionOn' with
    | h g =>
      have hdet := Matrix.SpecialLinearGroup.det_coe (g : SL(2, ℤ))
      rw [Matrix.det_fin_two] at hdet
      have hdet' := congrArg (Int.cast : ℤ → ZMod qc) hdet
      push_cast at hdet'
      obtain ⟨c', hc'⟩ : ((Mc : ℕ) : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := entry_dvd g
      refine ⟨(((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod qc) * ((c' : ℤ) : ZMod qc), ?_⟩
      show (Quotient.mk'' (lElt Mc _) : Quotient (QuotientGroup.rightRel
          (GammaHLower Mc (⊤ : Subgroup (ZMod Mc)ˣ) qc))) = Quotient.mk'' g
      rw [mk_eq_mk_iff_lower, mul_inv_apply_10]
      simp only [lElt_coe, lMat_10, lMat_11]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [show (g : SL(2, ℤ)) 1 0 * 1
            - (g : SL(2, ℤ)) 1 1 * (((((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod qc)
                * ((c' : ℤ) : ZMod qc)).val * (Mc : ℤ))
          = ((c' - ((((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod qc) * ((c' : ℤ) : ZMod qc)).val
              * (g : SL(2, ℤ)) 1 1) * (Mc : ℤ)) from by rw [hc']; ring]
      rw [show ((qc * Mc : ℕ) : ℤ) = (qc : ℤ) * (Mc : ℤ) from by push_cast; ring]
      refine mul_dvd_mul_right ?_ (Mc : ℤ)
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      have hcg : ((c' : ℤ) : ZMod qc) * ((Mc : ℕ) : ZMod qc) = 0 := by
        rw [hMq]; ring
      have hc'' := congrArg (Int.cast : ℤ → ZMod qc) hc'
      push_cast at hc''
      linear_combination (-(((c' : ℤ) : ZMod qc))) * hdet'
        - ((((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod qc) * (((c' : ℤ) : ZMod qc))) * hc''
        - ((((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod qc) * (((c' : ℤ) : ZMod qc))
            * (((c' : ℤ) : ZMod qc))) * hMq
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card, ZMod.card]

end LowerCount

private theorem lower_index_of_dvd :
    (GammaHLower (N * q) (⊤ : Subgroup (ZMod (N * q))ˣ) q).index = q := by
  rw [Subgroup.index, ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel
    (GammaHLower (N * q) (⊤ : Subgroup (ZMod (N * q))ˣ) q))]
  exact natCard_rightQuot_lower q (dvd_mul_left q N)

private theorem range_inner_1_eq_lower :
    (iotaDeg (N * q) (N * q ^ 2) ⊤ ⊤ 1 (levelLE_Nq_Nq2_1 N q)).range
      = GammaHLower (N * q) ⊤ q := by
  apply le_antisymm
  · rintro x ⟨γ', rfl⟩
    rw [Subgroup.mem_subgroupOf, Gamma0_mem, entry10 1 (levelLE_Nq_Nq2_1 N q) γ',
      Nat.cast_one, Int.ediv_one, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans ⟨1, by push_cast; ring⟩ (entry_dvd γ')
  · intro g hg
    rw [Subgroup.mem_subgroupOf, Gamma0_mem] at hg
    have hc : ((q * (N * q) : ℕ) : ℤ) ∣ ((g : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hg)
    refine ⟨⟨(g : ↥(GammaH (N * q) ⊤)), ?_⟩, ?_⟩
    · rw [GammaH_top, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact dvd_trans ⟨1, by push_cast; ring⟩ hc
    · apply Subtype.ext
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [iotaDeg, conjLowerMat, Matrix.of_apply, mul_one, Int.ediv_one]

private theorem lower_relindex_one
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1) :
    ((iotaDeg N (N * q ^ 2) ⊤ ⊤ 1 h1).range.subgroupOf (GammaHLower N ⊤ q)).index = q := by
  rw [lower_relindex_transport N q 1 (levelLE_Nq_Nq2_1 N q) h1,
    range_inner_1_eq_lower N q]
  exact lower_index_of_dvd N q

private theorem range_le_upper [NeZero (N * q ^ 2)] (d : ℕ) [NeZero d] (hqd : (q : ℤ) ∣ (d : ℤ))
    (h : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) d) :
    (iotaDeg N (N * q ^ 2) ⊤ ⊤ d h).range ≤ GammaHUpper N ⊤ q := by
  rintro x ⟨γ', rfl⟩
  rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper, entry01 d h γ']
  obtain ⟨e, he⟩ := hqd
  rw [he]
  push_cast
  rw [ZMod.natCast_self q]
  ring

private theorem upper_relindex [NeZero (N * q ^ 2)] (d : ℕ) [NeZero d]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (hqd : (q : ℤ) ∣ (d : ℤ))
    (h : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) d)
    (hidx : (iotaDeg N (N * q ^ 2) ⊤ ⊤ d h).range.index = q * (q + 1)) :
    ((iotaDeg N (N * q ^ 2) ⊤ ⊤ d h).range.subgroupOf (GammaHUpper N ⊤ q)).index = q := by
  have hm := Subgroup.relIndex_mul_index (range_le_upper N q d hqd h)
  rw [index_GammaHUpper_of_prime N ⊤ q hq hqN, hidx] at hm
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos q) hm

end Sol2Aux
p2m_reactivate "P2MW.S_CohCarrier_jDeg_iDeg_nine_identities_of_prime.Sol2Aux"

open CohCarrier

theorem solution (N q : ℕ) [NeZero N] [NeZero q]
    (A : Type) [AddCommGroup A] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2)) :
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (q * (q + 1) : ℤ) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ q A hq').comp (iDeg' N (N*q^2) ⊤ ⊤ q A hq') φ
        = (q * (q + 1) : ℤ) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (q * (q + 1) : ℤ) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ q A hq') φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ q A hq').comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ q A hq').comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ q A hq') φ
        = (q : ℤ) • heckeT N ⊤ q A φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (heckeT N ⊤ q A).comp (heckeT N ⊤ q A) φ - ((q : ℤ) + 1) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (heckeT N ⊤ q A).comp (heckeT N ⊤ q A) φ - ((q : ℤ) + 1) • φ) := by
  haveI : NeZero (N * q ^ 2) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (NeZero.ne q))⟩
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne q)⟩
  obtain ⟨hi1, hiq, hiq2⟩ := index_range_iotaDeg_of_prime_sq N q hq hqN h1 hq' hq2
  obtain ⟨c8, c9⟩ := jDeg_iDeg_corner_of_prime_sq N q A hq hqN h1 hq2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, c8, c9⟩ <;> intro φ
  · rw [AddMonoidHom.comp_apply, jDeg_comp_iDegP_self h1 φ, hi1, ← natCast_zsmul]
    congr 1
  · rw [AddMonoidHom.comp_apply, jDeg_comp_iDegP_self hq' φ, hiq, ← natCast_zsmul]
    congr 1
  · rw [AddMonoidHom.comp_apply, jDeg_comp_iDegP_self hq2 φ, hiq2, ← natCast_zsmul]
    congr 1
  · rw [AddMonoidHom.comp_apply,
      jDeg_iDeg_cross_eq_index_smul_heckeTlower hq hqN h1 hq'
        ⟨(N * q : ℤ), by push_cast; ring⟩ (one_mul q).symm φ,
      Sol2Aux.lower_relindex_one N q h1, heckeSym_top N q hq hqN φ]
    rw [← natCast_zsmul]
  · rw [AddMonoidHom.comp_apply,
      jDeg_iDeg_cross_eq_index_smul_heckeT q hq' h1 (dvd_refl _) (one_mul q).symm φ,
      Sol2Aux.upper_relindex N q q hq hqN (dvd_refl _) hq' hiq]
    rw [← natCast_zsmul]
  · rw [AddMonoidHom.comp_apply,
      jDeg_iDeg_cross_eq_index_smul_heckeTlower hq hqN hq' hq2
        ⟨(N : ℤ), by push_cast; ring⟩ (pow_two q) φ,
      Sol2Aux.lower_relindex_q N q hq', heckeSym_top N q hq hqN φ]
    rw [← natCast_zsmul]
  · rw [AddMonoidHom.comp_apply,
      jDeg_iDeg_cross_eq_index_smul_heckeT q hq2 hq' ⟨(q : ℤ), by push_cast; ring⟩
        (pow_two q) φ,
      Sol2Aux.upper_relindex N q (q ^ 2) hq hqN ⟨(q : ℤ), by push_cast; ring⟩ hq2 hiq2]
    rw [← natCast_zsmul]

end S_CohCarrier_jDeg_iDeg_nine_identities_of_prime
end P2MW
export P2MW.S_CohCarrier_jDeg_iDeg_nine_identities_of_prime (solution)
