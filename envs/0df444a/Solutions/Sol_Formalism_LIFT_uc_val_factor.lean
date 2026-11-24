-- Prove2me | solution 1 for Formalism.LIFT.uc_val_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:39:29.201802+00:00
-- url     : https://prove2.me/submissions/821194c5-e819-40f2-b577-25766d9a4e71

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
import Theorems.Thm_Formalism_WindowSums_valProd_of
import Theorems.Thm_Formalism_WindowSums_valuation_zpow_sub_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
namespace Formalism.LIFT
theorem _root_.solution (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (M s : ℕ) (J : Finset ℤ) (hs : 1 ≤ s)
    (h2 : ℓ = 2 → 2 ≤ s) (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s) (hJ : 0 ∉ J) :
    ∃ ν : ℤ_[ℓ], (ℓ : ℤ_[ℓ]) ^ eU ℓ M s J =
      ((∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
        ∏ i ∈ Finset.Icc 1 M, ((u : ℤ_[ℓ]) ^ i - 1)) * ν := by
  obtain ⟨hM, hJJ⟩ := Formalism.WindowSums.valProd_of Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hv
  obtain ⟨h2ne, h2v⟩ := hM M
  obtain ⟨h1ne, h1v⟩ := hJJ J hJ
  set P1 := ∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) with hP1
  set P2 := ∏ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i) with hP2
  have hcard : (Finset.Icc 1 M).card = M := by simp
  have hneg : ∏ i ∈ Finset.Icc 1 M, ((u : ℤ_[ℓ]) ^ i - 1) = (-1) ^ M * P2 := by
    have := Finset.prod_neg (s := Finset.Icc 1 M) (fun i => 1 - (u : ℤ_[ℓ]) ^ i)
    rw [hcard] at this
    rw [hP2, ← this]
    exact Finset.prod_congr rfl (fun i _ => by ring)
  have e1 := PadicInt.unitCoeff_spec h1ne
  have e2 := PadicInt.unitCoeff_spec h2ne
  set μ1 := PadicInt.unitCoeff h1ne
  set μ2 := PadicInt.unitCoeff h2ne
  have heU : eU ℓ M s J = P1.valuation + P2.valuation := by
    rw [h1v, h2v, eU, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]; ring
  refine ⟨((μ1⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((μ2⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (-1) ^ M, ?_⟩
  rw [heU, hneg, pow_add]
  have hm1 : ((-1 : ℤ_[ℓ]) ^ M) * (-1) ^ M = 1 := by rw [← mul_pow]; simp
  calc (ℓ : ℤ_[ℓ]) ^ P1.valuation * (ℓ : ℤ_[ℓ]) ^ P2.valuation
      = (ℓ : ℤ_[ℓ]) ^ P1.valuation * (ℓ : ℤ_[ℓ]) ^ P2.valuation *
          (((μ1 : ℤ_[ℓ]) * ((μ1⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) * ((μ2 : ℤ_[ℓ]) * ((μ2⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) *
            (((-1 : ℤ_[ℓ]) ^ M) * (-1) ^ M)) := by rw [Units.mul_inv, Units.mul_inv, hm1]; ring
    _ = ((μ1 : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ P1.valuation) *
          ((-1) ^ M * ((μ2 : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ P2.valuation)) *
          (((μ1⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((μ2⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (-1) ^ M) := by ring
    _ = P1 * ((-1) ^ M * P2) * (((μ1⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * ((μ2⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (-1) ^ M) := by
          rw [← e1, ← e2]
end Formalism.LIFT
