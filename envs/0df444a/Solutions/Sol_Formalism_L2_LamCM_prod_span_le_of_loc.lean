-- Prove2me | solution 1 for Formalism.L2.LamCM.prod_span_le_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:28:36.039019+00:00
-- url     : https://prove2.me/submissions/4f5ae589-99dd-4176-a742-308f699e370f

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_DetValuationLeOne
import Theorems.Thm_Formalism_L2_LamCM_le_one_of_count_nonneg
import Theorems.Thm_Formalism_L2_LamCM_valuation_eq_exp_count
import Theorems.Thm_P2M_Formalism_L2_LamCM_IsLocGen_mul__c4e282433e61
import Theorems.Thm_P2M_Formalism_L2_LamCM_IsLocGen_prod__e9d1965a7d60
import Theorems.Thm_P2M_Formalism_L2_LamCM_spanSingleton_ne_zero__ef0616425764


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM
theorem _root_.solution {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (d : K) (hLam : abelian₂.I ≠ 0)
    (hℓ : ∀ j, (ℓ j).I ≠ 0) (hd : d ≠ 0)
    (hloc : ∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin g → K), IsLocGen p cd abelian₂.I ∧
      (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * d) ≤ p.valuation K cd) :
    (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≤ abelian₂.I := by
  have hP : (∏ j, (ℓ j).I) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hℓ j
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 := spanSingleton_ne_zero' hd
  have hX0 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 := mul_ne_zero hP hs
  have h1 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d * abelian₂.I⁻¹ ≤ 1 := by
    apply le_one_of_count_nonneg (mul_ne_zero hX0 (inv_ne_zero hLam))
    intro p
    obtain ⟨cd, cl, hcd, hcl, hv⟩ := hloc p
    have hgen : IsLocGen p ((∏ j, cl j) * d) ((∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d) :=
      IsLocGen.mul' (IsLocGen.prod' Finset.univ cl (fun j => (ℓ j).I) hcl hℓ) ⟨hd, rfl⟩ hP hs
    rw [FractionalIdeal.count_mul K p hX0 (inv_ne_zero hLam), FractionalIdeal.count_inv, ← hgen.2, ← hcd.2]
    rw [valuation_eq_exp_count p hgen.1, valuation_eq_exp_count p hcd.1, WithZero.exp_le_exp] at hv
    omega
  calc (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d
      = (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d * abelian₂.I⁻¹ * abelian₂.I := by
        rw [mul_assoc _ abelian₂.I⁻¹, inv_mul_cancel₀ hLam, mul_one]
    _ ≤ 1 * abelian₂.I := mul_le_mul' h1 le_rfl
    _ = abelian₂.I := one_mul _
end Formalism.L2.LamCM
