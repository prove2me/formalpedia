-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.quadratic_top_algebra_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:39:57.82888+00:00
-- url     : https://prove2.me/submissions/7940dc15-b62e-4f87-9815-c1817e30d03b

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.GroupTheory.Perm.Support
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAlg_natDegree_prodP
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAlg_eval_prodP
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAlg_coeff_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
open Formalism.REAL
open TopAlg
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution : QTopAlg := by
  intro A _ _ n E h
  classical

  let lin : Equiv.Perm (Fin n) → Fin n → Prop := fun σ l => σ l = l
  let B : Equiv.Perm (Fin n) → Fin n → A := fun σ l =>
    (if σ l = l then algebraMap ℂ A (h - ((l : ℕ) : ℂ)) else 0) + E (σ l) l
  let Pσ : Equiv.Perm (Fin n) → A[X] := fun σ => prodP (lin σ) (B σ)
  refine ⟨fun j => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * (Pσ σ).coeff j, fun Y => ?_, fun hn => ?_⟩
  ·
    have hfac : ∀ σ : Equiv.Perm (Fin n),
        (List.ofFn fun k : Fin n => Tm E (Y + h - (k : ℂ)) (id (σ k)) (id k)).prod =
          ∑ j ∈ Finset.range (n + 1), Y ^ j • (Pσ σ).coeff j := by
      intro σ
      have e1 : (List.ofFn fun k : Fin n => Tm E (Y + h - (k : ℂ)) (id (σ k)) (id k)) =
          List.ofFn fun l => (if lin σ l then algebraMap ℂ A Y else 0) + B σ l := by
        congr 1
        funext l
        simp only [Tm, id, lin, B]
        split_ifs with hl
        · have : Y + h - ((l : ℕ) : ℂ) = Y + (h - ((l : ℕ) : ℂ)) := by ring
          rw [this, map_add]
          abel
        · simp
      rw [e1, ← eval_prodP]
      have hdeg : (Pσ σ).natDegree < n + 1 := by
        have := natDegree_prodP (lin σ) (B σ)
        have h2 : ∑ l : Fin n, (if lin σ l then 1 else 0) ≤ n := by
          calc ∑ l : Fin n, (if lin σ l then 1 else 0) ≤ ∑ _l : Fin n, 1 :=
                Finset.sum_le_sum fun l _ => by split_ifs <;> simp
            _ = n := by simp
        show (prodP (lin σ) (B σ)).natDegree < n + 1
        omega
      rw [eval₂_eq_sum_range' (RingHom.id A) hdeg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
    unfold qminor
    simp_rw [hfac, Finset.mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
  ·
    dsimp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul]
      have e1 : Pσ 1 = (List.ofFn fun l => (X + C (B 1 l) : A[X])).prod := by
        show prodP (lin 1) (B 1) = _
        unfold prodP fac
        congr 1
        congr 1
        funext l
        rw [if_pos (show lin 1 l from rfl)]
      rw [e1, (coeff_all (B 1)).2 hn]
      simp only [B, Equiv.Perm.one_apply, if_true]
      rw [Finset.sum_add_distrib, add_comm, ← map_sum]
      congr 1
      congr 1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hs : ∑ l : Fin n, ((l : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun l => ((l : ℕ) : ℂ)) n]
        have := Finset.sum_range_id_mul_two n
        have hc : ((∑ i ∈ Finset.range n, i : ℕ) : ℂ) * 2 = (n : ℂ) * ((n : ℂ) - 1) := by
          rw [← Nat.cast_ofNat, ← Nat.cast_mul, this]
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0; simp
          · rw [Nat.cast_mul, Nat.cast_sub (by omega)]
            simp
        push_cast at hc
        linear_combination hc / 2
      rw [hs]
    · intro σ _ hσ
      have h2 : 2 ≤ σ.support.card := Equiv.Perm.two_le_card_support_of_ne_one hσ
      have hdeg := natDegree_prodP (lin σ) (B σ)
      have hcount : ∑ l : Fin n, (if lin σ l then 1 else 0) + σ.support.card = n := by
        have hsupp : σ.support.card = ∑ l : Fin n, (if ¬ lin σ l then 1 else 0) := by
          rw [Finset.sum_boole, Nat.cast_id]
          rfl
        rw [hsupp, ← Finset.sum_add_distrib]
        calc ∑ l : Fin n, ((if lin σ l then 1 else 0) + (if ¬lin σ l then 1 else 0)) = ∑ _l : Fin n, 1 :=
              Finset.sum_congr rfl fun l _ => by split_ifs <;> simp_all
          _ = n := by simp
      have : (Pσ σ).coeff (n - 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by show (prodP (lin σ) (B σ)).natDegree < n - 1; omega)
      rw [this, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
