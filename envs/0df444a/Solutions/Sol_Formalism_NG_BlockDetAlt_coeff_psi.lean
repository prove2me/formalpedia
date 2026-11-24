-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.coeff_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:41.227446+00:00
-- url     : https://prove2.me/submissions/5420ce21-e650-466b-92b5-6549256a59ed

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {K : Type*} [CommRing K]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution (m : ℕ) (P : MvPolynomial (Fin m) K) :
    PowerSeries.coeff m (psi m P) =
      ∑ e ∈ Finset.Iic (bnd m), if wt e = m then MvPolynomial.coeff e P else 0 := by
  classical
  have hbnd : ∀ e : Fin m →₀ ℕ, wt e = m → e ∈ Finset.Iic (bnd m) := by
    intro e he
    rw [Finset.mem_Iic, Finsupp.le_def]
    intro j
    have hb : bnd m j = m := rfl
    rw [hb]
    have h1 : (j.1 + 1) * e j ≤ wt e :=
      Finset.single_le_sum (f := fun j : Fin m => (j.1 + 1) * e j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    calc e j ≤ (j.1 + 1) * e j := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ wt e := h1
      _ = m := he
  have hpsi : ∀ (e : Fin m →₀ ℕ) (c : K), psi m (MvPolynomial.monomial e c) =
      PowerSeries.C c * PowerSeries.X ^ wt e := by
    intro e c
    rw [psi, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp_rw [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  conv_lhs => rw [P.as_sum]
  rw [map_sum, map_sum]
  simp only [hpsi, PowerSeries.coeff_C_mul_X_pow]
  have h1 : ∑ e ∈ P.support, (if m = wt e then MvPolynomial.coeff e P else 0) =
      ∑ e ∈ P.support ∪ Finset.Iic (bnd m), (if m = wt e then MvPolynomial.coeff e P else 0) :=
    Finset.sum_subset Finset.subset_union_left (fun e _ he => by
      rw [MvPolynomial.notMem_support_iff.1 he]
      simp)
  have h2 : ∑ e ∈ Finset.Iic (bnd m), (if wt e = m then MvPolynomial.coeff e P else 0) =
      ∑ e ∈ P.support ∪ Finset.Iic (bnd m), (if wt e = m then MvPolynomial.coeff e P else 0) :=
    Finset.sum_subset Finset.subset_union_right (fun e _ he => if_neg (fun h => he (hbnd e h)))
  rw [h1, h2]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : wt e = m
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]
end Formalism.NG.BlockDetAlt
