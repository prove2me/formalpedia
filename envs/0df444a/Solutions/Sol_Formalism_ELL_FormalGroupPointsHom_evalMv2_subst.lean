-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.evalMv2_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:18.955072+00:00
-- url     : https://prove2.me/submissions/4212ad64-3ab7-4e6b-8e7a-83e273663b65

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_ev_apply
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_coeff_subst_two
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_coeff_mono_eq_zero
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_mul
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {G s t : MvPowerSeries (Fin 2) K} (hG : IntegralMv G) (hs : IntegralMv s)
    (ht : IntegralMv t) (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    evalMv2 (G.subst ![s, t]) a b = evalMv2 G (evalMv2 s a b) (evalMv2 t a b) := by
  set M : (Fin 2 →₀ ℕ) → MvPowerSeries (Fin 2) K := fun d => s ^ (d 0) * t ^ (d 1) with hMdef
  have hM : ∀ d, IntegralMv (M d) := fun d =>
    SubstitutionCoefficientCongruence.integral_mul (SubstitutionCoefficientCongruence.integral_pow hs _) (SubstitutionCoefficientCongruence.integral_pow ht _)
  have hMev : ∀ d, evalMv2 (M d) a b = evalMv2 s a b ^ (d 0) * evalMv2 t a b ^ (d 1) := by
    intro d
    have h := map_mul (ev a b ha hb) ((⟨s, hs⟩ : IL K) ^ (d 0)) ((⟨t, ht⟩ : IL K) ^ (d 1))
    rw [map_pow, map_pow] at h
    simpa [ev_apply, hMdef] using h
  set T : (Fin 2 →₀ ℕ) → (Fin 2 →₀ ℕ) → K := fun d e =>
    MvPowerSeries.coeff d G * (MvPowerSeries.coeff e (M d) * (a ^ (e 0) * b ^ (e 1))) with hT
  have hr0 : 0 ≤ max ‖a‖ ‖b‖ := le_trans (norm_nonneg a) (le_max_left _ _)
  have hsum : Summable (Function.uncurry T) := by
    refine summable_of_bound (fun x => x.2.degree) hr0 (max_lt ha hb) ?_ ?_
    · intro N
      refine ((finite_degree_lt N).prod (finite_degree_lt N)).subset ?_
      rintro ⟨d, e⟩ ⟨hne, hlt⟩
      simp only [Set.mem_prod, Set.mem_ofPred_eq]
      refine ⟨?_, hlt⟩
      by_contra hge
      push Not at hge
      apply hne
      simp only [Function.uncurry_apply_pair, hT]
      rw [coeff_mono_eq_zero hs0 ht0 (lt_of_lt_of_le hlt hge)]
      simp
    · rintro ⟨d, e⟩
      simp only [Function.uncurry_apply_pair, hT, norm_mul]
      have h1 := hG d
      have h2 := hM d e
      have h3 := norm_mono_le (le_max_left ‖a‖ ‖b‖) (le_max_right ‖a‖ ‖b‖) e
      rw [norm_mul] at h3
      calc ‖MvPowerSeries.coeff d G‖ * (‖MvPowerSeries.coeff e (M d)‖ * (‖a ^ (e 0)‖ * ‖b ^ (e 1)‖))
          ≤ 1 * (1 * max ‖a‖ ‖b‖ ^ e.degree) := by gcongr
        _ = _ := by ring
  have hL : evalMv2 (G.subst ![s, t]) a b = ∑' e, ∑' d, T d e := by
    rw [evalMv2_eq]
    congr 1; funext e
    have hfin : (Function.support fun d => MvPowerSeries.coeff d G *
        MvPowerSeries.coeff e (M d)).Finite := by
      refine (finite_degree_lt (e.degree + 1)).subset ?_
      intro d hd
      simp only [Set.mem_ofPred_eq]
      by_contra hge
      apply hd
      simp only [hMdef]
      rw [coeff_mono_eq_zero hs0 ht0 (by omega : e.degree < d.degree), mul_zero]
    have hfin' : (Function.support fun d => T d e).Finite := by
      refine hfin.subset ?_
      intro d hd h0
      apply hd
      have h0' : MvPowerSeries.coeff d G * MvPowerSeries.coeff e (M d) = 0 := h0
      simp only [hT]
      rw [← mul_assoc, h0', zero_mul]
    unfold term
    rw [coeff_subst_two G s t hs0 ht0 e, finsum_mul, tsum_eq_finsum hfin']
    congr 1; funext d
    simp only [hT, hMdef]; ring
  have hR : evalMv2 G (evalMv2 s a b) (evalMv2 t a b) = ∑' d, ∑' e, T d e := by
    rw [evalMv2_eq G (evalMv2 s a b) (evalMv2 t a b)]
    congr 1; funext d
    simp only [hT, term]
    rw [tsum_mul_left, ← hMev d, evalMv2_eq]
    rfl
  rw [hL, hR, hsum.tsum_comm]
end Formalism.ELL.FormalGroupPointsHom
