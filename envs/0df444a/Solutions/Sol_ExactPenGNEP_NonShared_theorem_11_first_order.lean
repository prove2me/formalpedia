-- Prove2me | solution 1 for ExactPenGNEP.NonShared.theorem_11_first_order
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:48:09.987079+00:00
-- url     : https://prove2.me/submissions/3d426d51-dccb-48a0-a138-6656e80aa7ac

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting
import Theorems.Thm_ExactPenGNEP_NonShared_eq_5_gradient

open Filter Topology LeiBR.Sync ExactPenGNEP.NonShared

lemma epg_affine_update_diff' {N : ℕ} {n : Fin N → ℕ} (f : Profile n →ᵃ[ℝ] ℝ) (x : Profile n)
    (ν : Fin N) : Differentiable ℝ (fun y : Strat n ν => f (Function.update x ν y)) := by
  let F : Profile n →ᴬ[ℝ] ℝ := ⟨f, f.continuous_of_finiteDimensional⟩
  have hF : Differentiable ℝ (fun z : Profile n => f z) := F.differentiable
  intro y
  exact (hF _).comp y (hasFDerivAt_update x y).differentiableAt

theorem solution {N : ℕ} {n m p : Fin N → ℕ} (C : ∀ ν, Set (Strat n ν))
    (g : ∀ ν, Fin (m ν) → Profile n → ℝ) (h : ∀ ν, Fin (p ν) → Profile n →ᵃ[ℝ] ℝ)
    (θ : Fin N → Profile n → ℝ) (Lip q ρ : ℝ) (xs : Profile n) (νh : Fin N) (xh : Strat n νh)
    (hCv : Convex ℝ (C νh)) (hLip : 0 < Lip)
    (hθ_cvx : ConvexOn ℝ (C νh) (fun y => θ νh (Function.update xs νh y)))
    (hθ_lip : LipschitzOnWith (Real.toNNReal Lip) (fun y => θ νh (Function.update xs νh y)) (C νh))
    (hg_diff : ∀ i, Differentiable ℝ (fun y => g νh i (Function.update xs νh y)))
    (hq : 1 < q) (hx : xs νh ∉ frSet g h νh xs) (hρ : 0 < ρ) (hmem : xs νh ∈ C νh)
    (hmin : ∀ y ∈ C νh,
      θ νh xs + ρ * lqRes (g νh) (fun j z => h νh j z) q xs ≤
        θ νh (Function.update xs νh y) +
          ρ * lqRes (g νh) (fun j z => h νh j z) q (Function.update xs νh y))
    (hxh : xh ∈ C νh) :
    ∃ θ' : ℝ,
      Tendsto (fun τ : ℝ => (θ νh (Function.update xs νh (xs νh + τ • (xh - xs νh))) - θ νh xs) / τ)
        (𝓝[>] 0) (𝓝 θ') ∧
      0 ≤ θ' + ρ * fderiv ℝ (fun y => lqRes (g νh) (fun j z => h νh j z) q
          (Function.update xs νh y)) (xs νh) (xh - xs νh) ∧
      θ' ≤ Lip * ‖xh - xs νh‖ := by
  classical
  set d := xh - xs νh with hd
  set f : Strat n νh → ℝ := fun y => θ νh (Function.update xs νh y) with hf
  have hf0 : f (xs νh) = θ νh xs := by simp [hf]
  -- the segment
  have hseg : ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 → xs νh + τ • d ∈ C νh := by
    intro τ hτ
    have := hCv.lineMap_mem hmem hxh hτ
    rwa [AffineMap.lineMap_apply_module', add_comm] at this
  let ℓ : ℝ →ᵃ[ℝ] Strat n νh := AffineMap.lineMap (xs νh) xh
  have hℓ : ∀ τ : ℝ, ℓ τ = xs νh + τ • d := by
    intro τ
    simp only [ℓ, AffineMap.lineMap_apply_module', hd]
    abel
  have hφcvx : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (f ∘ ℓ) := by
    refine (hθ_cvx.comp_affineMap ℓ).subset ?_ (convex_Icc 0 1)
    intro τ hτ
    simp only [Set.mem_preimage, hℓ]
    exact hseg τ hτ
  set Q : ℝ → ℝ := fun τ => (θ νh (Function.update xs νh (xs νh + τ • d)) - θ νh xs) / τ with hQ
  have hQf : ∀ τ, Q τ = ((f ∘ ℓ) τ - (f ∘ ℓ) 0) / (τ - 0) := by
    intro τ
    show _ = (f (ℓ τ) - f (ℓ 0)) / (τ - 0)
    rw [hℓ, hℓ, zero_smul, add_zero, hf0, sub_zero]
  -- monotonicity on (0,1]
  have hmono : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1 → Q a ≤ Q b := by
    intro a b ha hab hb1
    rw [hQf, hQf]
    exact hφcvx.secant_mono (a := 0) ⟨le_refl _, zero_le_one⟩ ⟨ha.le, hab.trans hb1⟩
      ⟨ha.le.trans hab, hb1⟩ ha.ne' (ha.trans_le hab).ne' hab
  -- Lipschitz bounds
  have hLipc : ((Real.toNNReal Lip : NNReal) : ℝ) = Lip := Real.coe_toNNReal _ hLip.le
  have hbound : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → |Q τ| ≤ Lip * ‖d‖ := by
    intro τ hτ hτ1
    have h1 := hθ_lip.dist_le_mul (x := xs νh + τ • d) (y := xs νh) (hseg τ ⟨hτ.le, hτ1⟩) hmem
    rw [hLipc, dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hτ.le, Real.norm_eq_abs, hf0] at h1
    rw [hQ]
    dsimp only
    rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
    calc _ ≤ Lip * (τ * ‖d‖) := h1
      _ = Lip * ‖d‖ * τ := by ring
  -- extension
  set Q' : ℝ → ℝ := fun τ => Q (min τ 1) with hQ'
  have hQ'mono : MonotoneOn Q' (Set.Ioi 0) := by
    intro a ha b hb hab
    simp only [hQ']
    exact hmono _ _ (lt_min ha one_pos) (min_le_min_right 1 hab) (min_le_right _ _)
  have hQ'bdd : BddBelow (Q' '' Set.Ioi 0) := by
    refine ⟨-(Lip * ‖d‖), ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    have := hbound (min τ 1) (lt_min hτ one_pos) (min_le_right _ _)
    simp only [hQ']
    linarith [neg_abs_le (Q (min τ 1))]
  have hlim' := hQ'mono.tendsto_nhdsGT hQ'bdd
  have hev : Q' =ᶠ[𝓝[>] 0] Q := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with τ hτ
    simp only [hQ', min_eq_left hτ.2.le]
  have hlim : Tendsto Q (𝓝[>] 0) (𝓝 (sInf (Q' '' Set.Ioi 0))) := hlim'.congr' hev
  have hev01 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ ∧ τ ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with τ hτ
    exact ⟨hτ.1, hτ.2.le⟩
  refine ⟨sInf (Q' '' Set.Ioi 0), hlim, ?_, ?_⟩
  · -- penalty derivative
    let G : Fin (m νh) → Strat n νh → ℝ := fun i y => g νh i (Function.update xs νh y)
    let H : Fin (p νh) → Strat n νh → ℝ := fun j y => h νh j (Function.update xs νh y)
    have hHd : ∀ j, Differentiable ℝ (H j) := fun j => epg_affine_update_diff' (h νh j) xs νh
    have hD := eq_5_gradient G H q (xs νh) hg_diff hHd hq hx
    have hfun : (fun y => lqRes (g νh) (fun j z => h νh j z) q (Function.update xs νh y)) =
        lqRes G H q := rfl
    rw [hfun, hD.fderiv]
    set D := (1 / lqRes G H q (xs νh) ^ (q - 1)) •
        (∑ i, (max (G i (xs νh)) 0) ^ (q - 1) • fderiv ℝ (G i) (xs νh) +
          ∑ j, (|H j (xs νh)| ^ (q - 1) * Real.sign (H j (xs νh))) • fderiv ℝ (H j) (xs νh))
      with hDdef
    have hline : HasDerivAt (fun τ : ℝ => xs νh + τ • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add (xs νh)
    have hR : HasDerivAt (lqRes G H q ∘ fun τ : ℝ => xs νh + τ • d) (D d) 0 :=
      hD.comp_hasDerivAt_of_eq 0 hline (by simp)
    have hRs := hR.tendsto_slope_zero_right
    have hsum := hlim.add (hRs.const_mul ρ)
    refine ge_of_tendsto hsum ?_
    filter_upwards [hev01] with τ hτ
    obtain ⟨hτ0, hτ1⟩ := hτ
    have hm := hmin (xs νh + τ • d) (hseg τ ⟨hτ0.le, hτ1⟩)
    have hR0 : (lqRes G H q ∘ fun τ : ℝ => xs νh + τ • d) 0 =
        lqRes (g νh) (fun j z => h νh j z) q xs := by
      simp only [Function.comp, zero_smul, add_zero]
      show lqRes (g νh) (fun j z => h νh j z) q (Function.update xs νh (xs νh)) = _
      rw [Function.update_eq_self]
    have hRτ : (lqRes G H q ∘ fun τ : ℝ => xs νh + τ • d) (0 + τ) =
        lqRes (g νh) (fun j z => h νh j z) q (Function.update xs νh (xs νh + τ • d)) := by
      simp only [Function.comp, zero_add]
      rfl
    rw [hR0, hRτ, smul_eq_mul]
    simp only [hQ]
    have key : 0 ≤ (θ νh (Function.update xs νh (xs νh + τ • d)) - θ νh xs) +
        ρ * (lqRes (g νh) (fun j z => h νh j z) q (Function.update xs νh (xs νh + τ • d)) -
          lqRes (g νh) (fun j z => h νh j z) q xs) := by linarith
    have : (θ νh (Function.update xs νh (xs νh + τ • d)) - θ νh xs) / τ +
        ρ * (τ⁻¹ * (lqRes (g νh) (fun j z => h νh j z) q
          (Function.update xs νh (xs νh + τ • d)) - lqRes (g νh) (fun j z => h νh j z) q xs)) =
        ((θ νh (Function.update xs νh (xs νh + τ • d)) - θ νh xs) +
        ρ * (lqRes (g νh) (fun j z => h νh j z) q (Function.update xs νh (xs νh + τ • d)) -
          lqRes (g νh) (fun j z => h νh j z) q xs)) / τ := by
      field_simp
    rw [this]
    exact div_nonneg key hτ0.le
  · refine le_of_tendsto hlim ?_
    filter_upwards [hev01] with τ hτ
    exact (le_abs_self _).trans (hbound τ hτ.1 hτ.2)
