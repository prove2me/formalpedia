-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF.jetSubstPS_eq_jetMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:18.59817+00:00
-- url     : https://prove2.me/submissions/80512b32-7ac7-4ac3-8e4f-84d5aeade02f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ESecToUnit
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSEqJetMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
variable {S : Type} [CommRing S] {κ κ' κ'' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [Fintype κ''] [DecidableEq κ'']
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
theorem _root_.solution (m : ℕ) (Q : κ → MvPowerSeries κ' S) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) :
    jetSubstPS (m := m) Q = jetMap (fun i => psTrunc m (Q i)) (fun i => psTrunc_mem_orig m (Q i) (hQ i)) := by
  unfold jetSubstPS
  congr 1
  funext i
  have h0 : MvPolynomial.constantCoeff (psTrunc m (Q i)) = 0 := by
    have hmem : (0 : κ' →₀ ℕ) ∈ degLE (ι := κ') m := by
      simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨fun _ => 0, ?_⟩, ?_⟩
      · ext j
        simp
      · simp
    rw [← hQ i]
    change MvPolynomial.coeff 0 (psTrunc m (Q i)) = _
    unfold psTrunc
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    rw [if_pos hmem]
    rfl
  rw [h0, map_zero, sub_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF
