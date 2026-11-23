-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmS_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:44.033068+00:00
-- url     : https://prove2.me/submissions/808089e7-68ac-484c-8a73-68858c196d63

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmS_rho_pos
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemmaSt_of
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmS_integral_sub_one
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (hGW : GenLogWeight.{u, 0}) (hGI : GenLogInverse.{u, 0}) (hB : LogBridges.{u})
    (hSW : SubstWt.{u, 0, 0}) (hQ : Quant.{u}) (hLS : LogStep.{u, 0})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l d : ℕ} [NeZero d]
    (hl : l.Prime) (hd : 2 ≤ d) (hde : Even d) (hpi : ‖(l : K)‖ < 1)
    {K0 : Subfield K} (hK0 : Unram l K0) (D : MvPowerSeries (V2 d) K)
    (hD0 : constantCoeff D = 0) (hK : ∀ n, coeff n (mvExp D) ∈ K0)
    (hcong : ∀ n : V2 d →₀ ℕ, coeff n (mvExp D) ≠ 0 →
      ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2)
    (hEi : Integral (subst (letterLog (K := K) l) (mvExp D)))
    (hEc : constantCoeff (subst (letterLog (K := K) l) (mvExp D)) = 1) :
    WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) D := by
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  have hρ : 0 ≤ rho l := (asmS_rho_pos hl).le
  have hLL : ∀ x : V2 d, letterLog (K := K) l x = genLog l (fun y : V2 d => (y.1, y.2 - 2)) x :=
    (hB K l d 0 0).1

  obtain ⟨g, hg0, hgl, -⟩ := hGI K l hl (V2 d) (fun y : V2 d => (y.1, y.2 - 2))
  have hgl' : ∀ x, subst g (letterLog (K := K) l x) = X x := fun x => by rw [hLL x]; exact hgl x
  have hgw : ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (g x) :=
    lemmaSt_of hGW hB K l d hl hpi g hg0 hgl'
  have hE1 := asmS_integral_sub_one hpi0 hpi.le hρ hEi hEc
  have hW := hSW K ‖(l : K)‖ hpi0 hpi (V2 d) (V2 d) g (fun _ => rho l) (fun _ => rho l) (rho l) _
    hg0 hgw hE1

  have hLL0 : ∀ x, constantCoeff (letterLog (K := K) l x) = 0 := fun x => by
    rw [← coeff_zero_eq_constantCoeff_apply]
    show letterLog (K := K) l x 0 = 0
    unfold letterLog
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    intro h
    have h' := congrArg (fun f : V2 d →₀ ℕ => f (x.1, x.2 - 2 * (e : ZMod d))) h
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at h'
    exact pow_ne_zero _ (pow_ne_zero _ hl.ne_zero) h'.symm
  have hLa : HasSubst (letterLog (K := K) l : V2 d → MvPowerSeries (V2 d) K) :=
    hasSubst_of_constantCoeff_zero hLL0
  have hga : HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hcomp : subst g (subst (letterLog (K := K) l) (mvExp D)) = mvExp D := by
    rw [subst_comp_subst_apply hLa hga, show (fun s => subst g (letterLog (K := K) l s)) = X from
      funext hgl', subst_self]
    rfl
  have hsub1 : subst g (subst (letterLog (K := K) l) (mvExp D) - 1) = mvExp D - 1 := by
    rw [← coe_substAlgHom hga, map_sub, map_one, coe_substAlgHom, hcomp]
  rw [hsub1] at hW

  have hQ' : WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (mvExp D - 1) := by
    intro n
    by_cases hz : coeff n (mvExp D - 1) = 0
    · unfold MonoWtGe
      rw [hz, norm_zero]
      exact (Real.rpow_pos_of_pos hpi0 _).le
    have hmem : coeff n (mvExp D - 1) ∈ K0 := by
      rw [map_sub, coeff_one]
      split_ifs
      · exact K0.sub_mem (hK n) K0.one_mem
      · exact K0.sub_mem (hK n) K0.zero_mem
    have hdiv : ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2 := by
      by_cases hn : n = 0
      · subst hn
        simp
      · apply hcong
        intro h0
        apply hz
        rw [map_sub, coeff_one, if_neg hn, h0, sub_zero]
    exact hQ K l d hl hd hde hpi hpi0 K0 hK0 _ hmem n hdiv (hW n)
  exact hLS K l hl hpi (V2 d) _ D hD0 hQ'
end Formalism.DworkPowerSeriesWeights
