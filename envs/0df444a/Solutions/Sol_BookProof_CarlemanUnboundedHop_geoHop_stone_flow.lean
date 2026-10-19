-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.geoHop_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T08:06:13.987696+00:00
-- url     : https://prove2.me/submissions/86290c06-31f7-4d72-9269-8891bd3e2873

import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterKernelBound
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_isL2Kernel
import Theorems.Thm_BookProof_CarlemanUnboundedHop_ladder_eq_zero_of_carleman
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_bound
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geo_hasSum_tail
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geo_summable_tail
import Theorems.Thm_BookProof_CarlemanUnboundedHop_not_summable_inv_one_add_nat
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_domain_dense
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.geoHop_stone_flow
open BookProof.EsaClosure
open BookProof.KernelBound
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.StoneBridge
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}
theorem h44_kop_symm {a : ℕ → ℕ → ℂ} (hk : BookProof.CarlemanUnboundedHop.IsL2Kernel a) :
    BookProof.FarisLavine.SymmetricOn (BookProof.NavierStokesFlow.lpFiniteModes ℕ) (BookProof.CarlemanUnboundedHop.kernelOp hk) := by
  intro x y
  obtain ⟨Nx, hNx⟩ := exists_tail_zero x.2
  obtain ⟨Ny, hNy⟩ := exists_tail_zero y.2
  set N := max Nx Ny
  have hx : ∀ n, N ≤ n → ((x : L2N) : ℕ → ℂ) n = 0 := fun n hn => hNx n (le_trans (le_max_left _ _) hn)
  have hy : ∀ n, N ≤ n → ((y : L2N) : ℕ → ℂ) n = 0 := fun n hn => hNy n (le_trans (le_max_right _ _) hn)
  rw [← inner_conj_symm, inner_eq_sum_range hy, inner_eq_sum_range hx]
  simp only [BookProof.CarlemanUnboundedHop.kernelOp_coe,
    BookProof.CarlemanUnboundedHop.kernelFun_eq_sum a hx, BookProof.CarlemanUnboundedHop.kernelFun_eq_sum a hy,
    map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hk.herm n k, Complex.conj_conj]
  ring

theorem h44_kop_def {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : BookProof.CarlemanUnboundedHop.IsL2Kernel a)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) {z : ℂ} (hz : z.im ≠ 0) :
    BookProof.FarisLavine.DeficiencyTrivialAt (BookProof.NavierStokesFlow.lpFiniteModes ℕ) (BookProof.CarlemanUnboundedHop.kernelOp hk) z := by
  intro w hw
  have hrow : ∀ n, Summable fun k => a n k * (w : ℕ → ℂ) k := by
    intro n
    have := lp.summable_inner (𝕜 := ℂ) (⟨fun k => a k n, hk.col n⟩ : L2N) w
    refine this.congr fun k => ?_
    simp only [RCLike.inner_apply]
    rw [hk.herm n k, Complex.conj_conj]; ring
  have heqn : ∀ n, ∑' k, a n k * (w : ℕ → ℂ) k = z * (w : ℕ → ℂ) n := by
    intro n
    have hs : (lp.single 2 n (1 : ℂ) : L2N) ∈ BookProof.NavierStokesFlow.lpFiniteModes ℕ := by
      refine mem_lpFiniteModes_of_tail_zero (N := n + 1) fun m hm => ?_
      rw [lp.single_apply, Pi.single_apply, if_neg (by omega)]
    have h1 := hw ⟨_, hs⟩
    have hK : ((BookProof.CarlemanUnboundedHop.kernelOp hk ⟨_, hs⟩ : L2N) : ℕ → ℂ) = fun m => a m n := by
      rw [BookProof.CarlemanUnboundedHop.kernelOp_coe]
      funext m
      rw [BookProof.CarlemanUnboundedHop.kernelFun_eq_sum a (M := n + 1)]
      · rw [Finset.sum_eq_single n]
        · simp
        · intro k _ hkn; simp [lp.single_apply, Pi.single_apply, hkn]
        · intro h; simp at h
      · intro m hm; simp only [lp.single_apply, Pi.single_apply]; rw [if_neg (by omega)]
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum] at h1
    simp only [RCLike.inner_apply, hK] at h1
    have h2 : ∑' i, (w : ℕ → ℂ) i * (starRingEnd ℂ) ((lp.single 2 n (1 : ℂ) : L2N) i) = (w : ℕ → ℂ) n := by
      rw [tsum_eq_single n]
      · simp [lp.single_apply]
      · intro m hm; simp [lp.single_apply, Pi.single_apply, hm]
    rw [h2] at h1
    rw [← h1]
    refine tsum_congr fun k => ?_
    rw [hk.herm n k, Complex.conj_conj]; ring
  have hu : Summable fun n => ‖(w : ℕ → ℂ) n‖ ^ 2 := by
    have := lp.memℓp w
    have h2 := this.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    simpa using h2
  have hz0 := BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman hz hk.herm ⟨hrow, heqn⟩ hu hθ0 hΘ hΘsum
    hApos hAmono hbd hcar
  ext n
  simpa using hz0 n

theorem solution (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    ∃ (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint L2N) (U : ℝ → (L2N →L[ℂ] L2N)),
      BookProof.EsaClosure.IsSelfAdjointExtension (kernelOp (geoHop_isL2Kernel b hrho hrho1)) T.op ∧
        BookProof.StoneBridge.IsStoneFlow T U := by
  have hk := geoHop_isL2Kernel b hrho hrho1
  have hθ0 : ∀ r : ℕ, 0 ≤ rho ^ r := fun r => pow_nonneg hrho r
  have hdef : ∀ z : ℂ, z.im ≠ 0 → BookProof.FarisLavine.DeficiencyTrivialAt (BookProof.NavierStokesFlow.lpFiniteModes ℕ)
      (BookProof.CarlemanUnboundedHop.kernelOp hk) z := fun z hz =>
    h44_kop_def hk (A := fun n => 1 + (n : ℝ)) (θ := fun r => rho ^ r)
      (Θ := fun j => rho ^ (j + 1) * (1 - rho)⁻¹) hθ0
      (fun j => BookProof.CarlemanUnboundedHop.geo_hasSum_tail hrho hrho1 j)
      (BookProof.CarlemanUnboundedHop.geo_summable_tail hrho hrho1)
      (fun n => by positivity)
      (fun m n hmn => by have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn; simp only; linarith)
      (fun n k hnk => BookProof.CarlemanUnboundedHop.geoHop_bound hrho n k hnk)
      BookProof.CarlemanUnboundedHop.not_summable_inv_one_add_nat hz
  exact BookProof.StoneBridge.exists_stone_flow_of_esa _
    BookProof.NavierStokesFlow.AffineFiber.affH_domain_dense (h44_kop_symm hk)
    ⟨hdef _ (by simp), hdef _ (by simp)⟩

