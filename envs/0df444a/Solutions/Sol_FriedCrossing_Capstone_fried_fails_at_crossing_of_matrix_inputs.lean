-- Prove2me | solution 1 for FriedCrossing.Capstone.fried_fails_at_crossing_of_matrix_inputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:09:47.177244+00:00
-- url     : https://prove2.me/submissions/ac15108c-df77-4b49-a1f0-29a27738914a

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Derived_finrank_resZero__f29bef30b26c
import Theorems.Thm_P2M_FriedCrossing_Derived_finrank_resZero__43df11cc6bdc
import Theorems.Thm_FriedCrossing_Derived_clusterC1_of_C3
import Theorems.Thm_FriedCrossing_Derived_traceDetC1_of_C3
import Theorems.Thm_FriedCrossing_Derived_pureSumC2_of_C3
import Theorems.Thm_FriedCrossing_Derived_pureProdC3_of_C3
import Theorems.Thm_P2M_FriedCrossing_Spectral_E__mirror_535f6e567606
import Theorems.Thm_P2M_FriedCrossing_Spectral_E__mirror_bf3c94cb1a0c
import Theorems.Thm_P2M_FriedCrossing_Spectral_E__pinned_89a5c3e78b6a
import Theorems.Thm_P2M_FriedCrossing_Spectral_E__pinned_8575cb4e933f
import Theorems.Thm_FriedCrossing_Spectral_rootMultiplicity_zero_fin_two
import Theorems.Thm_FriedCrossing_Spectral_crossing_pure_data
import Theorems.Thm_FriedCrossing_Branch_zBranch_root
import Theorems.Thm_FriedCrossing_Branch_zBranch_at_simple_zero
import Theorems.Thm_FriedCrossing_Capstone_fried_fails_at_crossing_of_pure_zero_inputs_ord
import Theorems.Thm_FriedCrossing_FirstVariation_Nmat_unique
import Theorems.Thm_FriedCrossing_FirstVariation_det_Nmat
import Theorems.Thm_FriedCrossing_FirstVariation_trace_Nmat
import Theorems.Thm_FriedCrossing_Hadamard_M_eq
import Theorems.Thm_FriedCrossing_Hadamard_Ndiv_zero
import Theorems.Thm_FriedCrossing_Hadamard_continuousAt_det_Ndiv
import Theorems.Thm_FriedCrossing_Hadamard_continuousAt_trace_Ndiv
import Theorems.Thm_FriedCrossing_Hadamard_det_M
import Theorems.Thm_FriedCrossing_Hadamard_trace_M
import Theorems.Thm_FriedCrossing_OrderCount_finrank_middle_of_exact
import Theorems.Thm_FriedCrossing_OrderCount_order_zero_of_exact
import Theorems.Thm_FriedCrossing_TwinRate_branches_ne
import Theorems.Thm_FriedCrossing_TwinRate_twin_rate_of_cluster
import Theorems.Thm_FriedCrossing_TwinRate_twin_zero
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_add_wMinus
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_mul_wMinus


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Capstone
open TwinRate Hadamard FirstVariation Derived Spectral ClusterMatrix Ledger OrderCount TorsionCore
  Regularity Branch
namespace FriedCrossing.Capstone
theorem _root_.solution
    {V₃ : Type*} [AddCommGroup V₃] [Module ℝ V₃]
    (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (sStar : ℝ → ℝ) (Bcc Bcψ Bψc Bψψ p : ℝ)
    (hsemisimple : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hC3 : ClusterC3 M A)
    (hdet : Bcc * Bψψ - Bcψ * Bψc ≠ 0)
    (h422 : Bmat Bcc Bcψ Bψc Bψψ * Mτ M 0 0 = Pmat p)
    (hr₀ : 0 < Bcc * p / (Bcc * Bψψ - Bcψ * Bψc))
    (hsStar0 : sStar 0 = 0) (hsStarc : ContinuousAt sStar 0)
    (hsStarneg : ∀ θ, θ ≠ 0 → sStar θ < 0)
    (hmirror : ∀ θ z, (A θ 0).charpoly.eval z = (z - sStar θ) ^ 3 * (z + sStar θ))
    (hpinned : Pinned M A)
    (hlocked : ∀ θ τ z, (M θ τ).charpoly.eval z = 0 → (A θ τ).charpoly.eval z = 0) :
    let a : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M (Mτ M) sStar θ τ).trace
    let b : ℝ → ℝ → ℝ := fun θ τ => (Ndiv M (Mτ M) sStar θ τ).det
    let a' : ℝ → ℝ → ℝ := aτ M
    let b' : ℝ → ℝ → ℝ := bτ M sStar
    let e₁ : ℝ → ℝ → ℝ := E₁f M A
    let e₂ : ℝ → ℝ → ℝ := E₂f M A
    let e₂τ : ℝ → ℝ → ℝ := pτ e₂
    let z : ℝ → ℝ → ℝ := fun θ => zBranch (e₁ θ) (e₂ θ)
    let r₀ : ℝ := Bcc * p / (Bcc * Bψψ - Bcψ * Bψc)
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∃ θ₀ δ : ℝ, 0 < θ₀ ∧ 0 < δ ∧ ∀ θ, θ ≠ 0 → |θ| < θ₀ →
      ∀ (ζ₀ F : ℝ → ℝ) (c : Fin 5 → ℕ) (τR : ℝ),
        τR ≠ 0 →
        ZetaFactorization ζ₀ F (twin sStar a b θ) (z θ) δ →
        (∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → ζ₀ τ = τR) →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          ∃ (f : resZero₁ M θ τ₀ →ₗ[ℝ] resZero₂ A θ τ₀) (g : resZero₂ A θ τ₀ →ₗ[ℝ] V₃),
            Function.Injective f ∧ LinearMap.range f = LinearMap.ker g ∧ Function.Surjective g) →
        (c 0 = 0 ∧ c 4 = 0) → c 3 = c 1 →
        (∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
          c 1 = Module.finrank ℝ (resZero₁ M θ τ₀) ∧ c 2 = Module.finrank ℝ (resZero₂ A θ τ₀) ∧
          c 3 = Module.finrank ℝ V₃) →
        ∃ σ, 0 < σ ∧ σ ≤ 2 * |sStar θ| / r₀ ∧ σ < δ ∧ twin sStar a b θ σ = 0 ∧
          (∀ τ, |τ| < δ → twin sStar a b θ τ = 0 → τ = σ) ∧
          zetaOrder c = 0 ∧
          HasDerivAt (z θ) (e₂τ θ σ / e₁ θ σ) σ ∧ 2 * r₀ < |e₂τ θ σ / e₁ θ σ| ∧
          |e₁ θ σ| ≤ K₁ * |θ| * σ ∧
          ∃ α ratio : ℝ, α ≠ 0 ∧ dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ ≠ 0 ∧
            Tendsto (fun τ => twin sStar a b θ τ / z θ τ) (𝓝[≠] σ) (𝓝 ratio) ∧
            ratio = dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ / α ∧ ratio ≠ 1 ∧
            ζ₀ σ = τR * ratio ∧ ζ₀ σ ≠ τR ∧
            refinedTorsion 1 (dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ /
              (α - dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ)) =
              -(α / dtwin (a θ σ) (b θ σ) (a' θ σ) (b' θ σ) σ) := by
  intro a b a' b' e₁ e₂ e₂τ z r₀
  -- the derived bundles
  have hC1 := clusterC1_of_C3 hC3
  have hTD := traceDetC1_of_C3 hC3 hsemisimple
  obtain ⟨K₁, hS⟩ := pureSumC2_of_C3 hC3
  obtain ⟨K₂, hP⟩ := pureProdC3_of_C3 hC3
  -- (4.22) pins a(0,0) = r₀, b(0,0) = 0
  have hM00 : Mτ M 0 0 = Nmat Bcc Bcψ Bψc Bψψ p := Nmat_unique hdet _ h422
  have ha0 : a 0 0 = r₀ := by
    change (Ndiv M (Mτ M) sStar 0 0).trace = _
    rw [Ndiv_zero, hM00, trace_Nmat]
  have hb0 : b 0 0 = 0 := by
    change (Ndiv M (Mτ M) sStar 0 0).det = 0
    rw [Ndiv_zero, hM00, det_Nmat]
  have hcont_a : ContinuousAt (Function.uncurry a) (0, 0) :=
    continuousAt_trace_Ndiv M (Mτ M) sStar hsemisimple hC1.deriv hC1.cont
  have hcont_b : ContinuousAt (Function.uncurry b) (0, 0) :=
    continuousAt_det_Ndiv M (Mτ M) sStar hsemisimple hC1.deriv hC1.cont
  -- the rate lemma: positive discriminant on an ε₁-square
  obtain ⟨ε₁, hε₁, hrate⟩ := twin_rate_of_cluster sStar a b a' b' hr₀ hTD.deriv_a hTD.deriv_b
    hcont_a hcont_b hTD.cont_a' hTD.cont_b' ha0 hb0
  -- mirror and pinning values
  have h₁τ0 : ∀ θ, e₁ θ 0 = 0 := fun θ => E₁_mirror (hsemisimple θ) (hmirror θ)
  have h₂τ0 : ∀ θ, e₂ θ 0 = -(sStar θ) ^ 2 := fun θ => E₂_mirror (hsemisimple θ) (hmirror θ)
  have h₁θ0 : ∀ τ, e₁ 0 τ = 0 := fun τ => E₁_pinned (hpinned.deg2 τ)
  have h₂θ0 : ∀ τ, e₂ 0 τ = 0 := fun τ => E₂_pinned (hpinned.deg1 τ) (hpinned.deg2 τ)
  -- the square: ε := min 1 ε₁ (bounds hold on the unit square, discriminant on the ε₁-square)
  have hε : 0 < min 1 ε₁ := lt_min one_pos hε₁
  obtain ⟨θ₀, δ, hθ₀, hδ, hθ₀ε, hδε, H⟩ :=
    fried_fails_at_crossing_of_pure_zero_inputs_ord
      sStar a b a' b' hr₀ hTD.deriv_a hTD.deriv_b hcont_a hcont_b hTD.cont_a' hTD.cont_b' ha0 hb0
      hsStar0 hsStarc hsStarneg e₁ e₂ (pτ e₁) (pθ (pτ e₁)) (pτ e₂) (pτ (pτ e₂))
      (pθ (pτ (pτ e₂))) hS.K_pos hP.K_pos hε hS.deriv_τ hS.deriv_θτ
      (fun θ τ hθ hτ => hS.bound θ τ (lt_of_lt_of_le hθ (min_le_left _ _))
        (lt_of_lt_of_le hτ (min_le_left _ _)))
      hP.deriv_τ hP.deriv_ττ hP.deriv_θττ
      (fun θ τ hθ hτ => hP.bound θ τ (lt_of_lt_of_le hθ (min_le_left _ _))
        (lt_of_lt_of_le hτ (min_le_left _ _)))
      h₁τ0 h₁θ0 h₂τ0 h₂θ0
  refine ⟨K₁, hS.K_pos, θ₀, δ, hθ₀, hδ, fun θ hθne hθ ζ₀ F c τR hτR hCD
    hfried_off hexact hacyc hdual hdims => ?_⟩
  have hθε₁ : |θ| < ε₁ := lt_of_lt_of_le hθ (le_trans hθ₀ε (min_le_right _ _))
  -- the exactness dictionary at each crossing: e₂ = 0, e₁ ≠ 0
  have hzc : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 →
      ContinuousAt (z θ) τ₀ ∧ z θ τ₀ = 0 ∧ e₂ θ τ₀ = 0 ∧ e₁ θ τ₀ ≠ 0 := by
    intro τ₀ hτ₀ h0
    have hτ₀ε₁ : |τ₀| < ε₁ := lt_of_lt_of_le hτ₀ (le_trans hδε (min_le_right _ _))
    have hdisc : 0 < disc (a θ τ₀) (b θ τ₀) := (hrate θ τ₀ hθε₁ hτ₀ε₁).1
    have hτ₀ne : τ₀ ≠ 0 := by
      rintro rfl
      rw [twin_zero] at h0
      exact (hsStarneg θ hθne).ne h0
    -- the locked branches: s_cl = s* + τ₀w₋, s_nc = twin = s* + τ₀w₊
    have hsnc : twin sStar a b θ τ₀ = sStar θ + τ₀ * wPlus (a θ τ₀) (b θ τ₀) := rfl
    have hne : sStar θ + τ₀ * wMinus (a θ τ₀) (b θ τ₀) ≠ twin sStar a b θ τ₀ := by
      rw [hsnc]; exact (branches_ne hτ₀ne hdisc).symm
    have hMτ : M θ τ₀ = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + τ₀ • Ndiv M (Mτ M) sStar θ τ₀ :=
      M_eq M (Mτ M) sStar hsemisimple θ τ₀
    have hs : (sStar θ + τ₀ * wMinus (a θ τ₀) (b θ τ₀)) + twin sStar a b θ τ₀ =
        (M θ τ₀).trace := by
      rw [hsnc, hMτ, trace_M, clusterTrace]
      have := wPlus_add_wMinus (a θ τ₀) (b θ τ₀)
      change _ = 2 * sStar θ + τ₀ * a θ τ₀
      linear_combination τ₀ * this
    have hp : (sStar θ + τ₀ * wMinus (a θ τ₀) (b θ τ₀)) * twin sStar a b θ τ₀ =
        (M θ τ₀).det := by
      rw [hsnc, hMτ, det_M, clusterDet]
      have h1 := wPlus_add_wMinus (a θ τ₀) (b θ τ₀)
      have h2 := wPlus_mul_wMinus hdisc.le
      change _ = sStar θ ^ 2 + sStar θ * τ₀ * a θ τ₀ + τ₀ ^ 2 * b θ τ₀
      linear_combination (sStar θ * τ₀) * h1 + τ₀ ^ 2 * h2
    -- c₁ = 1, hence c₂ = 2 by exactness (dimensions = multiplicities: Mathlib)
    obtain ⟨hc1, hc2, hc3⟩ := hdims τ₀ hτ₀ h0
    have hf1 := finrank_resZero₁ M θ τ₀
    have hf2 := finrank_resZero₂ A θ τ₀
    have hc1' : c 1 = 1 := by
      rw [hc1, hf1]; exact rootMultiplicity_zero_fin_two hne h0 hs hp
    obtain ⟨f, g, hf, hfg, hg⟩ := hexact τ₀ hτ₀ h0
    have hmid := finrank_middle_of_exact f g hf hfg hg
    have hc2' : (A θ τ₀).charpoly.rootMultiplicity 0 = 2 := by omega
    obtain ⟨hE₂, hE₁⟩ := crossing_pure_data hne h0 hs hp (hlocked θ τ₀) hc2'
    -- the defined branch is continuous through 0 there
    obtain ⟨hzc, hz0⟩ := zBranch_at_simple_zero (e₁ := e₁ θ) (e₂ := e₂ θ)
      (hS.deriv_τ θ τ₀).continuousAt (hP.deriv_τ θ τ₀).continuousAt hE₂ hE₁
    exact ⟨hzc, hz0, hE₂, hE₁⟩
  -- the ζ-order at each crossing, from exactness
  have hord : ∀ τ₀, |τ₀| < δ → twin sStar a b θ τ₀ = 0 → zetaOrder c = 0 := by
    intro τ₀ hτ₀ h0
    obtain ⟨f, g, hf, hfg, hg⟩ := hexact τ₀ hτ₀ h0
    exact order_zero_of_exact f g hf hfg hg c hacyc hdual (hdims τ₀ hτ₀ h0)
  -- CD (6.5) off the crossing + DGRS constancy ⇒ the old `hfried_off` shape for F
  have hfo : ∀ τ, |τ| < δ → twin sStar a b θ τ ≠ 0 → F τ * z θ τ / twin sStar a b θ τ = τR :=
    fun τ hτ hne => by rw [← hCD.off τ hτ hne]; exact hfried_off τ hτ hne
  obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7, h8, h9, α, ratio, hα, hb, hlim, hreq, hr1, hval, hne,
      htors⟩ :=
    H θ hθne hθ (z θ) F c τR hτR (fun τ hD => zBranch_root (e₁ θ) (e₂ θ) τ hD) hzc hCD.cont hfo
      hord
  refine ⟨σ, h1, h2, h3, h4, h5, h6, h7, h8, h9, α, ratio, hα, hb, hlim, hreq, hr1, ?_, ?_, htors⟩
  · rw [hCD.at_crossing σ h4]; exact hval
  · rw [hCD.at_crossing σ h4]; exact hne
end FriedCrossing.Capstone
