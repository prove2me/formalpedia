-- Prove2me | solution 1 for Formalism.FG.CongrVAux.coeff_subst_perturb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:55:25.982873+00:00
-- url     : https://prove2.me/submissions/b24a8c3f-9a86-4b1e-b2bc-5b3bf490c805

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Theorems.Thm_Formalism_FG_SolveVAux_P_single
import Theorems.Thm_Formalism_FG_SolveVAux_degree_eq_one
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow_sub_succ


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
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {R : Type u} [CommRing R] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution {ι : Type v} [Fintype ι] {d : τ →₀ ℕ} (hd : d ≠ 0)
    {k : ι → MvPowerSeries τ R} (hk : ∀ i, constantCoeff (k i) = 0) (c : ι → R)
    (g : MvPowerSeries ι R) :
    coeff d (subst (fun i => k i + monomial d (c i)) g) =
      coeff d (subst k g) + ∑ i, coeff (Finsupp.single i 1) g * c i := by
  classical
  set k' : ι → MvPowerSeries τ R := fun i => k i + monomial d (c i) with hk'def
  have hm0 : ∀ i, constantCoeff (monomial d (c i) : MvPowerSeries τ R) = 0 := fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial_ne (Ne.symm hd)]
  have hk'0 : ∀ i, constantCoeff (k' i) = 0 := fun i => by
    simp only [hk'def, map_add, hk i, hm0 i, add_zero]
  have hs := hasSubst_of_constantCoeff_zero hk
  have hs' := hasSubst_of_constantCoeff_zero hk'0
  have hdiff : ∀ i, k' i - k i = monomial d (c i) := fun i => by simp [hk'def]
  have hlow : ∀ i, Low d.degree (k' i - k i) := fun i e he => by
    rw [hdiff i, coeff_monomial_ne]
    rintro rfl; exact lt_irrefl _ he
  have hT : ∀ e : ι →₀ ℕ, coeff e g • coeff d (e.prod fun s n => k' s ^ n) -
      coeff e g • coeff d (e.prod fun s n => k s ^ n) =
      if e ∈ Finset.univ.image (fun i => Finsupp.single i 1) then
        coeff e g • coeff d (e.prod fun s n => k' s ^ n) -
          coeff e g • coeff d (e.prod fun s n => k s ^ n) else 0 := by
    intro e
    split_ifs with he
    · rfl
    rw [← smul_sub, ← map_sub]
    rcases Nat.lt_or_ge e.degree 2 with h2 | h2
    · rcases Nat.lt_or_ge e.degree 1 with h1 | h1
      · have : e = 0 := (Finsupp.degree_eq_zero_iff e).1 (by omega)
        subst this
        simp
      · obtain ⟨i, rfl⟩ := degree_eq_one e (by omega)
        exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩) he
    · have := low_pow_sub_succ (fun i => (low_one_iff _).2 (hk'0 i)) (fun i => (low_one_iff _).2 (hk i))
        hlow e h2 d (by omega)
      simp only [P] at this
      rw [this, smul_zero]
  have hsum : coeff d (subst k' g) - coeff d (subst k g) =
      ∑ i, coeff (Finsupp.single i 1) g * c i := by
    rw [coeff_subst hs', coeff_subst hs,
      ← finsum_sub_distrib (coeff_subst_finite hs' g d) (coeff_subst_finite hs g d),
      finsum_congr hT, finsum_eq_sum_of_support_subset _
        (s := Finset.univ.image (fun i => Finsupp.single i 1))]
    · rw [Finset.sum_ite_of_true (fun _ h => h), Finset.sum_image]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← smul_sub, ← map_sub]
        change coeff _ g • coeff d (P k' (Finsupp.single i 1) - P k (Finsupp.single i 1)) = _
        rw [P_single, P_single, pow_one, pow_one, hdiff i, coeff_monomial_same, smul_eq_mul]
      · intro i _ j _ hij
        exact Finsupp.single_left_injective one_ne_zero hij
    · intro e he
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at he
      obtain ⟨h, _⟩ := he
      exact h
  linear_combination hsum
end Formalism.FG.CongrVAux
