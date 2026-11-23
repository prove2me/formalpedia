-- Prove2me | solution 1 for Formalism.FG.InjVAux.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:37.291357+00:00
-- url     : https://prove2.me/submissions/f4486907-34e3-4d68-b51b-cc2e148ba792

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mono
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_sub
import Theorems.Thm_Formalism_FG_InjVAux_Good_pow
import Theorems.Thm_Formalism_FG_InjVAux_good_prod
import Theorems.Thm_Formalism_FG_InjVAux_eq_single_of_degree_eq_one
import Theorems.Thm_Formalism_FG_InjVAux_hasOrd_one_of_cc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
open Formalism.FG.InjVAux
open MvPowerSeries
variable {R : Type*} [CommRing R] {τ : Type*}
namespace Formalism.FG.InjVAux
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Finite τ]
    (f : ι → MvPowerSeries ι R) (a b : ι → MvPowerSeries τ R) (hf : IsIdMod2 f)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (h : ∀ j, subst a (f j) = subst b (f j)) :
    ∀ N, ∀ i, HasOrd (N + 1) (a i - b i) := by
  have haS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hbS : HasSubst b := hasSubst_of_constantCoeff_zero hb
  intro N
  induction N with
  | zero => intro i; exact (hasOrd_one_of_cc (ha i)).sub (hasOrd_one_of_cc (hb i))
  | succ N ih =>
    intro j d hd
    have hgood : ∀ i, Good N 1 (a i) (b i) :=
      fun i => ⟨hasOrd_one_of_cc (ha i), hasOrd_one_of_cc (hb i), ih i⟩
    have hj := congrArg (coeff d) (h j)
    rw [coeff_subst haS, coeff_subst hbS] at hj
    have hdiff := congrArg (fun t => t - finsum (fun e : ι →₀ ℕ =>
      coeff e (f j) • coeff d (e.prod fun s n => b s ^ n))) hj
    simp only [sub_self] at hdiff
    rw [← finsum_sub_distrib (coeff_subst_finite haS (f j) d)
      (coeff_subst_finite hbS (f j) d)] at hdiff
    rw [finsum_eq_single _ (Finsupp.single j 1)] at hdiff
    · rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
        hf.2 j j, if_pos rfl, one_smul, one_smul, pow_one, pow_one] at hdiff
      rw [map_sub, hdiff]
    · intro e he
      rw [← smul_sub, ← map_sub]
      rcases Nat.lt_or_ge e.degree 2 with hlt | hge
      · rcases Nat.lt_or_ge e.degree 1 with h0 | h1
        · have : e = 0 := (Finsupp.degree_eq_zero_iff e).1 (by omega)
          subst this
          simp
        · obtain ⟨i, rfl⟩ := eq_single_of_degree_eq_one e (by omega)
          have hij : i ≠ j := fun hij => he (by rw [hij])
          rw [hf.2 j i, if_neg hij, zero_smul]
      · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
          Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
        have hg := good_prod Finset.univ (fun i => 1 * e i) (fun i => a i ^ e i)
          (fun i => b i ^ e i) (fun i _ => (hgood i).pow (e i))
        have hsum : ∑ i ∈ Finset.univ, 1 * e i = e.degree := by
          rw [Finsupp.degree_eq_sum]; simp
        rw [hsum] at hg
        rw [hg.2.2.mono (n := N + e.degree) (by omega) d hd, smul_zero]
end Formalism.FG.InjVAux
