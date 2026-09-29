-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9689e016-bbb9-5a6a-97d5-b756f5f51669

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct
p2m_open "LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega~DrinfeldDatum~stalk"

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
    (c c' : κ) (hcc' : c * c' = 0) (hc : c = 0 ∨ c ^ p ≠ c) (hc' : c' = 0 ∨ c' ^ p ≠ c') :
    ∃ d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ,
      d.line (stdFullLattice ℚ_[p]) =
          Submodule.span κ {c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} ∧
        d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
          (Submodule.span κ {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
            (actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap := by
  classical

  have hp0 : algebraMap ℤ_[p] κ (p : ℤ_[p]) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero κ p
  have hB : IsNilpotent (algebraMap ℤ_[p] κ (p : ℤ_[p])) := by rw [hp0]; exact IsNilpotent.zero

  have hq : Nat.card (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) = p := by
    have hI : Ideal.span {(p : ℤ_[p])} = RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
    have e := (Ideal.quotEquivOfEq hI).trans
      (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZMod (p := p))))
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

  have hunit : ∀ a : κ, (a = 0 ∨ a ^ p ≠ a) → IsUnit (a ^ (p - 1) - 1) := by
    intro a ha
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    intro h
    rcases ha with rfl | ha
    · rw [zero_pow (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)] at h
      exact zero_ne_one h
    · apply ha
      have hp : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos).symm
      conv_lhs => rw [hp, pow_succ, h, one_mul]

  have hx : (c, c').1 * (c, c').2 = algebraMap ℤ_[p] κ (p : ℤ_[p]) ∧ IsUnit ((c, c').1 ^ (p - 1) - 1) ∧
      IsUnit ((c, c').2 ^ (p - 1) - 1) := ⟨by rw [hp0]; exact hcc', hunit c hc, hunit c' hc'⟩
  obtain ⟨d, h0, h1, -⟩ := CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
    (p : ℤ_[p]) PadicInt.irreducible_p p hq g hg κ hB
    (chartERing.lift (⟨(c, c'), hx⟩ : (chartE ℤ_[p] (p : ℤ_[p]) p).obj κ))
  rw [chartERing.lift_ξ] at h0
  rw [chartERing.lift_η] at h1
  exact ⟨d, h0, h1⟩

end S_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP (solution)
