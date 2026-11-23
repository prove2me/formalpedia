-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.term_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:59.151838+00:00
-- url     : https://prove2.me/submissions/c288a1b0-cba9-42a0-9492-b2dfdad90447

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_Fz_uni
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
section GlobalTheory
variable {K : Type} [CommRing K] {a s N : ℕ}
variable (hN : N = a + s) (A A' : Matrix (Fin a) (Fin a) K) (B B' : Matrix (Fin a) (Fin s) K)
    (C C' : Matrix (Fin s) (Fin a) K) (D D' : Matrix (Fin s) (Fin s) K)
end GlobalTheory
section Phi
variable {K : Type} [CommRing K] (R : Subring K)
end Phi
section Simple
variable {K : Type} [CommRing K] {a s N : ℕ}
end Simple
section Lists
variable {K : Type} [CommRing K]
end Lists
section Cls
variable {K : Type} [CommRing K] (R : Subring K) {ι κ μ : Type}
end Cls
section Grp
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
end Grp
section PhiInv
variable {K : Type} [CommRing K] (R : Subring K)
variable {a s : ℕ}
variable {N : ℕ}
end PhiInv
section Pert
variable {K : Type} [CommRing K] (R : Subring K)
end Pert
section Sum
variable {K : Type} [CommRing K] (R : Subring K) {h g w : Point K}
  (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
private lemma sLow_mul_lemma {n : ℕ} {a b : Matrix (Fin n) (Fin n) K} (ha : IsLowUni a)
    (hb : IsLowUni b) : sLow (a * b) = sLow a + sLow b := by
  unfold sLow
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rw [Matrix.mul_apply, Finset.sum_eq_add j ⟨j + 1, hj⟩]
    · rw [hb.2 j, ha.2 ⟨j + 1, hj⟩, mul_one, one_mul]
    · intro h
      have := congrArg Fin.val h
      simp at this
    · intro c _ hc
      by_cases hcj : c < j
      · rw [hb.1 hcj, mul_zero]
      · have hlt : (⟨j + 1, hj⟩ : Fin n) < c := by
          rw [Fin.lt_iff_val_lt_val]
          have h1 : (c : ℕ) ≠ j := fun e => hc.1 (Fin.ext e)
          have h2 : (c : ℕ) ≠ j + 1 := fun e => hc.2 (Fin.ext e)
          have h3 : (j : ℕ) ≤ c := by
            have := not_lt.1 hcj
            exact this
          show (j : ℕ) + 1 < c
          omega
        rw [ha.1 hlt, zero_mul]
    · simp
    · simp
  · simp
private lemma sUp_mul_lemma {n : ℕ} {a b : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a)
    (hb : IsUpUni b) : sUp (a * b) = sUp a + sUp b := by
  unfold sUp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rw [Matrix.mul_apply, Finset.sum_eq_add j ⟨j + 1, hj⟩]
    · rw [ha.2 j, hb.2 ⟨j + 1, hj⟩, mul_one, one_mul, add_comm]
    · intro h
      have := congrArg Fin.val h
      simp at this
    · intro c _ hc
      by_cases hcj : c < j
      · rw [ha.1 hcj, zero_mul]
      · have hlt : (⟨j + 1, hj⟩ : Fin n) < c := by
          rw [Fin.lt_iff_val_lt_val]
          have h1 : (c : ℕ) ≠ j := fun e => hc.1 (Fin.ext e)
          have h2 : (c : ℕ) ≠ j + 1 := fun e => hc.2 (Fin.ext e)
          have h3 : (j : ℕ) ≤ c := by
            have := not_lt.1 hcj
            exact this
          show (j : ℕ) + 1 < c
          omega
        rw [hb.1 hlt, mul_zero]
    · simp
    · simp
  · simp
private lemma sLow_mem_lemma {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsInt R x) : sLow x ∈ R := by
  unfold sLow
  exact sum_mem fun j _ => by
    split_ifs
    exacts [hx _ _, zero_mem _]
private lemma sUp_mem_lemma {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsInt R x) : sUp x ∈ R := by
  unfold sUp
  exact sum_mem fun j _ => by
    split_ifs
    exacts [hx _ _, zero_mem _]
end Sum
section Fin
variable {K : Type} [CommRing K] (R : Subring K)
end Fin
end Formalism.FourierDecayAlt.P.TwoBlockPoint
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K) {h g w : Point K}
  (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w : Point K) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (p p₁ : lowW K w.1 w.2 × upUniG K w.1.sum)
    (hp : toCos R p = toCos R p₁) :
    Fz R Z' (orbZ w p) * phase ψ p = Fz R Z' (orbZ w p₁) * phase ψ p₁ := by
  simp only [toCos, Prod.mk.injEq] at hp
  obtain ⟨hq1, hq2⟩ := hp
  obtain ⟨k, hk, e1⟩ := (sec_right_eq _ _ _).1 hq1
  rw [QuotientGroup.eq] at hq2
  set m := p.2⁻¹ * p₁.2 with hm
  have e2 : p₁.2 = p.2 * m := by rw [hm, mul_inv_cancel_left]
  have hk1 : IsLowUni (sec_m k) := k.2.1
  have hk2 : IsInt R (sec_m k) := hk.1
  have hm1 : IsUpUni (sec_m m) := m.2
  have hm2 : IsInt R (sec_m m) := hq2.1
  have eo : orbZ w p₁ = sec_m k * orbZ w p * sec_m m := by
    unfold orbZ
    rw [e1, e2]
    simp only [Subgroup.coe_mul, Units.val_mul, sec_m, Matrix.mul_assoc]
  have ep : phase ψ p₁ = phase ψ p * ψ (sLow (sec_m k) + sUp (sec_m m)) := by
    unfold phase
    rw [e1, e2]
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [sLow_mul_lemma hk1 p.1.2.1, sUp_mul_lemma p.2.2 hm1, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have h1 : ψ (sLow (sec_m k) + sUp (sec_m m)) = 1 :=
    hψ _ (add_mem (sLow_mem_lemma R hk2) (sUp_mem_lemma R hm2))
  rw [eo, ep, h1, mul_one, Fz_uni R Z' _ _ _ hk1 hk2 hm1 hm2]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
