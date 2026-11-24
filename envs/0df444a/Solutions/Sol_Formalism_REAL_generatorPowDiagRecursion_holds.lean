-- Prove2me | solution 1 for Formalism.REAL.generatorPowDiagRecursion_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:20.861182+00:00
-- url     : https://prove2.me/submissions/3e69a2d5-551b-4e63-b1e6-058eedb6000e

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag
import Theorems.Thm_Formalism_REAL_HWDiag_covApply
import Theorems.Thm_Formalism_REAL_HWDiag_upper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.REAL
private theorem epow_succ_apply {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (k : ℕ) (a b : Fin n) : epow E (k + 1) a b = ∑ c, epow E k a c * E c b := by
  first | rfl | simp [epow]
private theorem module_end_mul_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f g : Module.End ℂ V) (v : V) : (f * g) v = f (g v) := rfl
private theorem module_end_finset_sum_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    (s : Finset ι) (f : ι → Module.End ℂ V) (v : V) : (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  first
  | exact LinearMap.sum_apply s f v
  | simp
  | (classical
     induction s using Finset.induction_on with
     | empty => simp
     | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, LinearMap.add_apply, ih])
private theorem card_filter_fin_lt_eq {n : ℕ} (a : Fin n) :
    (univ.filter fun b : Fin n => a < b).card = n - 1 - (a : ℕ) := by
  first
  | (rw [show (univ.filter fun b : Fin n => a < b) = Finset.Ioi a by ext; simp]
     exact Fin.card_Ioi a)
  | (have hmap : (univ.filter fun b : Fin n => a < b).map Fin.valEmbedding =
        Finset.Ico ((a : ℕ) + 1) n := by
       ext x
       simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
         Fin.valEmbedding_apply, Finset.mem_Ico]
       constructor
       · rintro ⟨b, hb, rfl⟩
         exact ⟨Nat.succ_le_of_lt hb, b.isLt⟩
       · rintro ⟨h1, h2⟩
         exact ⟨⟨x, h2⟩, Fin.lt_def.mpr (by simpa using h1), rfl⟩
     rw [← Finset.card_map Fin.valEmbedding, hmap, Nat.card_Ico]
     omega)
private theorem cast_nat_sub_one_sub_fin_eq_complex {n : ℕ} (a : Fin n) :
    ((n - 1 - (a : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - (a : ℂ) := by
  have ha := a.isLt
  have hN : n - 1 - (a : ℕ) + (a : ℕ) + 1 = n := by omega
  have hc : ((n - 1 - (a : ℕ) : ℕ) : ℂ) + (a : ℂ) + 1 = (n : ℂ) := by
    first
    | exact_mod_cast hN
    | (have h' := congrArg (Nat.cast : ℕ → ℂ) hN
       push_cast at h'
       exact h')
  linear_combination hc
end Formalism.REAL
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : HWDiag := by
  unfold HWDiag
  intro V _i1 _i2 n E ν v hE hv k a
  have hv' : (∀ a, E a a v = ν a • v) ∧ ∀ a b, a < b → E a b v = 0 := hv
  have hterm : ∀ c : Fin n, epow E k a c (E c a v) =
      (if c = a then ν a • epow E k a a v else 0) +
        (if a < c then epow E k a a v - epow E k c c v else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | hca | hca
    · rw [hv'.2 c a hca, map_zero]
      simp [hca.ne, not_lt.mpr hca.le]
    · rw [hca, hv'.1 a, map_smul]
      simp
    · rw [HWDiag_covApply E hE k a c c a v,
        HWDiag_upper E ν v hE hv k a c hca, map_zero]
      simp [hca.ne', hca]
  have h1 : (∑ c : Fin n, if c = a then ν a • epow E k a a v else 0) =
      ν a • epow E k a a v := by
    simp
  have h2 : (∑ c : Fin n, if a < c then epow E k a a v - epow E k c c v else 0) =
      ∑ c ∈ univ.filter (fun b => a < b), (epow E k a a v - epow E k c c v) := by
    rw [Finset.sum_filter]
  have hsmul : (n - 1 - (a : ℕ)) • epow E k a a v =
      ((n : ℂ) - 1 - (a : ℂ)) • epow E k a a v := by
    rw [← cast_nat_sub_one_sub_fin_eq_complex a]
    first
    | exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm
    | exact nsmul_eq_smul_cast ℂ _ _
    | simp
  rw [epow_succ_apply, module_end_finset_sum_apply]
  simp only [module_end_mul_apply, hterm]
  rw [Finset.sum_add_distrib, h1, h2, Finset.sum_sub_distrib, Finset.sum_const,
    card_filter_fin_lt_eq, hsmul]
  simp only [lsh, add_smul]
  abel
end Formalism.REAL
