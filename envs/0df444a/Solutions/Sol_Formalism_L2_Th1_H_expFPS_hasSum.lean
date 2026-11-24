-- Prove2me | solution 1 for Formalism.L2.Th1.H.expFPS_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:35:53.557797+00:00
-- url     : https://prove2.me/submissions/c0541638-1385-4d96-bab1-41ab1478c0d4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
import Theorems.Thm_Formalism_L2_Th1_H_powForm_diag
import Theorems.Thm_Formalism_L2_Th1_H_summable_norm_expTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ)
    (h : ∀ r : ℝ, Summable fun x => ‖c x‖ * Real.exp (r * ‖l x‖)) (y : V) :
    HasSum (fun n => expFPS c l n fun _ => y) (∑' x, c x * Complex.exp (l x y)) := by
  have hterm : ∀ n x, expTerm c l n x (fun _ => y) = c x * (l x y) ^ n / (n ! : ℂ) := by
    intro n x
    rw [expTerm, ContinuousMultilinearMap.smul_apply, powForm_diag, smul_eq_mul]
    ring
  have hev : ∀ n, expFPS c l n (fun _ => y) = ∑' x, c x * (l x y) ^ n / (n ! : ℂ) := by
    intro n
    have hs : HasSum (fun x => expTerm c l n x) (expFPS c l n) :=
      (Summable.of_norm (summable_norm_expTerm c l h n)).hasSum
    have h1 := hs.mapL (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => V) ℂ (fun _ => y))
    exact h1.tsum_eq.symm.trans (tsum_congr fun x => hterm n x)
  let g : X × ℕ → ℂ := fun p => c p.1 * (l p.1 y) ^ p.2 / (p.2 ! : ℂ)
  have hfib : ∀ x, HasSum (fun n => g (x, n)) (c x * Complex.exp (l x y)) := by
    intro x
    have h1 := NormedSpace.expSeries_div_hasSum_exp (l x y)
    rw [← Complex.exp_eq_exp_ℂ] at h1
    have h2 := h1.mul_left (c x)
    simpa [g, mul_div_assoc] using h2
  have hg : ∀ p : X × ℕ, ‖g p‖ = ‖c p.1‖ * (‖l p.1 y‖ ^ p.2 / (p.2 ! : ℝ)) := by
    intro p
    have hn : ‖((p.2 ! : ℕ) : ℂ)‖ = (p.2 ! : ℝ) := by simp
    simp only [g, norm_div, norm_mul, norm_pow, hn]
    ring
  have hnorm : Summable fun p : X × ℕ => ‖g p‖ := by
    simp_rw [hg]
    rw [summable_prod_of_nonneg (fun _ => by positivity)]
    refine ⟨fun x => by simpa using (Real.summable_pow_div_factorial ‖l x y‖).mul_left ‖c x‖, ?_⟩
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) (h ‖y‖)
    have he := NormedSpace.expSeries_div_hasSum_exp (‖l x y‖)
    rw [← Real.exp_eq_exp_ℝ] at he
    dsimp only
    rw [tsum_mul_left, he.tsum_eq]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have := (l x).le_opNorm y
    linarith [mul_comm ‖y‖ ‖l x‖]
  have hsum : Summable g := hnorm.of_norm
  have htot : HasSum g (∑' x, c x * Complex.exp (l x y)) := by
    have h1 := hsum.hasSum
    rw [hsum.tsum_prod' (fun x => (hfib x).summable)] at h1
    have e : (fun b => ∑' n, g (b, n)) = fun b => c b * Complex.exp (l b y) :=
      funext fun b => (hfib b).tsum_eq
    rw [e] at h1
    exact h1
  have hswap : HasSum (fun p : ℕ × X => g (p.2, p.1)) (∑' x, c x * Complex.exp (l x y)) :=
    (Equiv.prodComm ℕ X).hasSum_iff.2 htot
  have hfin := hswap.prod_fiberwise (fun n => (hswap.summable.prod_factor n).hasSum)
  convert hfin using 1
  funext n
  rw [hev n]
end Formalism.L2.Th1.H
