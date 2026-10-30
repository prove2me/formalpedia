-- Prove2me | solution 1 for DerivativeChainContinuation.real_derivative_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:35:27.4774+00:00
-- url     : https://prove2.me/submissions/a61ade4e-3d91-43b6-9f05-8ff79d27958e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_strict_real_derivative_interlacing
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators
open Filter Topology


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial Filter Topology
open scoped BigOperators

theorem realRootProduct_eval_continuous (n : ℕ) (x : ℝ) :
    Continuous (fun a : Fin n → ℝ => (realRootProduct a).eval x) := by
  simp only [realRootProduct, eval_prod, eval_sub, eval_X, eval_C]
  fun_prop

theorem realRootProduct_derivative_eval_continuous (n : ℕ) (x : ℝ) :
    Continuous (fun a : Fin n → ℝ => (realRootProduct a).derivative.eval x) := by
  simp [realRootProduct, derivative_prod_finset, eval_finsetSum, eval_prod]
  fun_prop




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (a : Fin (n+2) → ℝ)
    (ha : Monotone a) :
    ∃ b : Fin (n+1) → ℝ, Monotone b ∧
      (∀ i, a i.castSucc ≤ b i ∧ b i ≤ a i.succ) ∧
      (realRootProduct a).derivative = C (n+2 : ℝ) * realRootProduct b := by
  classical
  let eps : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have hep (k : ℕ) : 0 < eps k := by dsimp [eps]; positivity
  have he1 (k : ℕ) : eps k ≤ 1 := by dsimp [eps]; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have helim : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let aa : ℕ → Fin (n+2) → ℝ := fun k i => a i + eps k * (i.val : ℝ)
  have hstrict (k : ℕ) : StrictMono (aa k) := by
    intro i j hij
    have hc : (i.val : ℝ) < j.val := by exact_mod_cast hij
    have hh := mul_lt_mul_of_pos_left hc (hep k)
    have hm := ha hij.le
    dsimp [aa]; linarith
  have halim : Tendsto aa atTop (𝓝 a) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa [aa] using tendsto_const_nhds.add (helim.mul_const (i.val : ℝ))
  choose b hb using fun k => strict_real_derivative_interlacing n (aa k) (hstrict k)
  let lo : Fin (n+1) → ℝ := fun _ => a 0
  let hi : Fin (n+1) → ℝ := fun _ => a (Fin.last (n+1)) + (n+1 : ℝ)
  have hbox (k : ℕ) : b k ∈ Set.Icc lo hi := by
    constructor <;> intro i
    · have h := (hb k).2.1 i
      have hm := ha (show (0 : Fin (n+2)) ≤ i.castSucc by exact Fin.zero_le _)
      have he : 0 ≤ eps k * (i.val : ℝ) := by positivity
      dsimp [aa] at h
      dsimp [lo]; linarith [h.1]
    · have h := (hb k).2.1 i
      have hm := ha (show i.succ ≤ Fin.last (n+1) by exact Fin.le_last _)
      have hn : ((i.succ).val : ℝ) ≤ (n+1 : ℝ) := by exact_mod_cast (show i.succ.val ≤ n+1 by omega)
      have he := mul_le_mul_of_nonneg_right (he1 k) (show (0 : ℝ) ≤ i.succ.val by positivity)
      dsimp [aa] at h
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, one_mul] at hn he
      dsimp [hi]; push_cast at h; linarith [h.2]
  obtain ⟨w,_,phi,hphi,hlim⟩ := (isCompact_Icc : IsCompact (Set.Icc lo hi)).tendsto_subseq hbox
  have ha' := halim.comp hphi.tendsto_atTop
  have hw (i : Fin (n+1)) : Tendsto (fun k => b (phi k) i) atTop (𝓝 (w i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hlim
  have ha'coord (i : Fin (n+2)) : Tendsto (fun k => aa (phi k) i) atTop (𝓝 (a i)) :=
    (continuous_apply i).continuousAt.tendsto.comp ha'
  refine ⟨w,?_,?_,?_⟩
  · intro i j hij
    exact le_of_tendsto_of_tendsto (hw i) (hw j)
      (Eventually.of_forall fun k => (hb (phi k)).1.monotone hij)
  · intro i
    exact ⟨le_of_tendsto_of_tendsto (ha'coord i.castSucc) (hw i)
      (Eventually.of_forall fun k => ((hb (phi k)).2.1 i).1.le),
      le_of_tendsto_of_tendsto (hw i) (ha'coord i.succ)
      (Eventually.of_forall fun k => ((hb (phi k)).2.1 i).2.le)⟩
  · apply Polynomial.funext
    intro x
    have hl := (realRootProduct_derivative_eval_continuous (n+2) x).continuousAt.tendsto.comp ha'
    have hr := ((realRootProduct_eval_continuous (n+1) x).continuousAt.tendsto.comp hlim).const_mul (n+2 : ℝ)
    have heq : (fun k => (realRootProduct (aa (phi k))).derivative.eval x) =
        (fun k => (n+2 : ℝ) * (realRootProduct (b (phi k))).eval x) := by
      funext k
      rw [(hb (phi k)).2.2, eval_mul, eval_C]
    simp only [Function.comp_def] at hl hr
    rw [heq] at hl
    simpa only [eval_mul, eval_C] using tendsto_nhds_unique hl hr
