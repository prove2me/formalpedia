-- Prove2me | solution 1 for Formalism.DegreeFormula.PFlagDeg.coeff_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:02.978132+00:00
-- url     : https://prove2.me/submissions/c0f0506f-d70e-40a3-abe2-94005771fd91

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg
import Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_prod_perm_rev
import Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_permExp_apply
import Theorems.Thm_P2M_Formalism_DegreeFormula_PFlagDeg_permExp_sum__8b8ff68e0568
import Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_linRoot_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg
set_option maxRecDepth 4000
namespace Formalism.DegreeFormula.PFlagDeg
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (lam : ι → Fin N → ℝ)
    (σ : ι → Equiv.Perm (Fin N)) :
    (linRoot lam ^ dimFl ι N).coeff (permExp σ) =
      (-1) ^ dimFl ι N * (((dimFl ι N).factorial : ℝ) / ((sfac N : ℝ) ^ Fintype.card ι)) *
        ∏ τ, ∏ i : Fin N, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ)) := by
  have hterm : ∀ k : ι × Fin N → ℕ,
      ((Nat.multinomial Finset.univ k : ℕ) : MvPolynomial (ι × Fin N) ℝ) *
          ∏ x, ((-lam x.1 x.2) • (X x : MvPolynomial (ι × Fin N) ℝ)) ^ k x =
        monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial Finset.univ k : ℝ) * ∏ x, (-lam x.1 x.2) ^ k x) := by
    intro k
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), C_mul, map_prod]
    simp only [smul_pow, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, map_pow, map_natCast,
      Finsupp.coe_equivFunOnFinite_symm]
    ring
  have hsum : ∑ x : ι × Fin N, (N - 1 - ((σ x.1 x.2 : Fin N) : ℕ)) = dimFl ι N := by
    rw [← permExp_sum' σ]
    simp only [permExp_apply]
  have hfac : ∏ x : ι × Fin N, (N - 1 - ((σ x.1 x.2 : Fin N) : ℕ)).factorial =
      sfac N ^ Fintype.card ι := by
    rw [Fintype.prod_prod_type,
      Finset.prod_congr rfl (fun τ _ => prod_perm_rev (σ τ) Nat.factorial), Finset.prod_const,
      Finset.card_univ]
    rfl
  rw [linRoot_eq, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp only [hterm, coeff_monomial]
  rw [Finset.sum_eq_single (fun x : ι × Fin N => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ))]
  · rw [if_pos (show Finsupp.equivFunOnFinite.symm
        (fun x : ι × Fin N => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ)) = permExp σ from rfl)]
    have hm : ((Nat.multinomial Finset.univ
        (fun x : ι × Fin N => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ)) : ℕ) : ℝ) =
        ((dimFl ι N).factorial : ℝ) / ((sfac N : ℝ) ^ Fintype.card ι) := by
      have hs := Nat.multinomial_spec Finset.univ
        (fun x : ι × Fin N => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ))
      rw [hfac, hsum] at hs
      have hpos : ((sfac N : ℝ) ^ Fintype.card ι) ≠ 0 := by
        apply pow_ne_zero
        unfold sfac
        exact_mod_cast (Finset.prod_pos fun i _ => Nat.factorial_pos _).ne'
      rw [eq_div_iff hpos, mul_comm]
      exact_mod_cast hs
    have hp : ∏ x : ι × Fin N, (-lam x.1 x.2) ^ (N - 1 - ((σ x.1 x.2 : Fin N) : ℕ)) =
        (-1) ^ dimFl ι N * ∏ τ, ∏ i : Fin N, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ)) := by
      rw [Finset.prod_congr rfl (fun x _ => neg_pow (lam x.1 x.2) (N - 1 - ((σ x.1 x.2 : Fin N) : ℕ))),
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, Fintype.prod_prod_type]
    rw [hm, hp]
    ring
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk (Finsupp.equivFunOnFinite.symm.injective h)
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    exact ⟨hsum, fun i _ => Finset.mem_univ i⟩
end Formalism.DegreeFormula.PFlagDeg
