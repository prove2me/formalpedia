-- Prove2me | solution 1 for DynReinsDiv.HJB.lemma_A_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:58:28.03604+00:00
-- url     : https://prove2.me/submissions/e4359956-166f-4ef0-be55-266febf8404d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model
import Definitions.Def_DynReinsDiv_HJB_PDE
import Theorems.Thm_DynReinsDiv_HJB_lemma_A_2
import Theorems.Thm_DynReinsDiv_HJB_eq_A_21

open DynReinsDiv.HJB Set Filter Topology

namespace DynReinsDiv.HJB.A4Aux

/-- The model with the shorter horizon `T - Δ`. -/
def shorten (M : Model) (Δ : ℝ) (hΔ : Δ < M.T) : Model :=
  { M with T := M.T - Δ, T_pos := by linarith }

/-- (A.20) via Lemma A.2: `u(x, s) ≤ u(x, s + Δ)`. -/
theorem shift_le (M : Model) (L lam ε : ℝ) (hL : 0 < L) (hlam : 0 < lam) (hroot : M.fA lam = 0)
    (hε : 0 < ε) (β fε : ℝ → ℝ) (hβ : IsPenalty M ε β) (hf : IsRamp ε lam fε)
    (u ux uxx ut : ℝ → ℝ → ℝ) (hC : IsC21RectClosed L M.T u ux uxx ut)
    (hS : SolvesPenalized M L lam β fε u ux uxx ut)
    (hge : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 1 ≤ u x t)
    (Δ : ℝ) (hΔ : 0 < Δ) (hΔT : Δ < M.T) :
    ∀ x s : ℝ, 0 < x → x < L → 0 < s → s ≤ M.T - Δ → u x s ≤ u x (s + Δ) := by
  set M' := shorten M Δ hΔT with hM'
  have hT' : M'.T = M.T - Δ := rfl
  have hβ' : IsPenalty M' ε β :=
    ⟨hβ.smooth, hβ.at_zero, hβ.vanish, hβ.nonpos, hβ.deriv_nonneg, hβ.deriv2_nonpos⟩
  have hroot' : M'.fA lam = 0 := hroot
  have hsub : Icc 0 L ×ˢ Icc 0 (M.T - Δ) ⊆ Icc 0 L ×ˢ Icc 0 M.T :=
    prod_mono le_rfl (Icc_subset_Icc le_rfl (by linarith))
  -- u on the shorter rectangle
  have h₁ : IsC21Rect L M'.T u ux uxx ut := by
    rw [hT']
    refine ⟨hC.cont.mono hsub, hC.cont_ux.mono ?_, hC.cont_uxx.mono ?_, hC.cont_ut.mono ?_,
      fun x t hx hxL ht htT => hC.deriv_x x t hx hxL ht (by linarith),
      fun x t hx hxL ht htT => hC.deriv_xx x t hx hxL ht (by linarith),
      fun x t hx hxL ht htT => hC.deriv_t x t hx hxL ht (by linarith)⟩
    · exact prod_mono Ico_subset_Icc_self (fun t ht => ⟨ht.1.le, by linarith [ht.2]⟩)
    · exact prod_mono Ioo_subset_Icc_self (fun t ht => ⟨ht.1.le, by linarith [ht.2]⟩)
    · exact prod_mono Ioo_subset_Icc_self (fun t ht => ⟨ht.1.le, by linarith [ht.2]⟩)
  -- the time-shifted function
  have hmaps : ∀ s : Set ℝ, s ⊆ Icc 0 L → ∀ a b : ℝ, 0 ≤ a → b ≤ M.T - Δ →
      MapsTo (fun p : ℝ × ℝ => (p.1, p.2 + Δ)) (s ×ˢ Icc a b) (Icc 0 L ×ˢ Icc 0 M.T) := by
    intro s hs a b ha hb p hp
    exact ⟨hs hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  have hcomp : Continuous (fun p : ℝ × ℝ => (p.1, p.2 + Δ)) :=
    continuous_fst.prodMk (continuous_snd.add continuous_const)
  have h₂ : IsC21Rect L M'.T (fun x t => u x (t + Δ)) (fun x t => ux x (t + Δ))
      (fun x t => uxx x (t + Δ)) (fun x t => ut x (t + Δ)) := by
    rw [hT']
    refine ⟨?_, ?_, ?_, ?_, fun x t hx hxL ht htT => hC.deriv_x x (t + Δ) hx hxL (by linarith)
        (by linarith), fun x t hx hxL ht htT => hC.deriv_xx x (t + Δ) hx hxL (by linarith)
        (by linarith), fun x t hx hxL ht htT => ?_⟩
    · exact hC.cont.comp hcomp.continuousOn (hmaps _ subset_rfl 0 _ le_rfl le_rfl)
    · exact (hC.cont_ux.comp hcomp.continuousOn (hmaps _ Ico_subset_Icc_self 0 _ le_rfl le_rfl)).mono
        (prod_mono subset_rfl Ioc_subset_Icc_self)
    · refine hC.cont_uxx.comp hcomp.continuousOn ?_
      intro p hp
      exact ⟨Ioo_subset_Icc_self hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
    · refine hC.cont_ut.comp hcomp.continuousOn ?_
      intro p hp
      exact ⟨Ioo_subset_Icc_self hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
    · have := hC.deriv_t x (t + Δ) hx hxL (by linarith) (by linarith)
      exact this.comp_add_const t Δ
  have key := lemma_A_2 M' L lam ε hL hlam hroot' hε β hβ' u ux uxx ut
    (fun x t => u x (t + Δ)) (fun x t => ux x (t + Δ)) (fun x t => uxx x (t + Δ))
    (fun x t => ut x (t + Δ)) h₁ h₂ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x s hx hxL hs hsT
    exact key x s hx hxL hs (by rw [hT']; exact hsT)
  · intro x t hx hxL ht htT
    rw [hT'] at htT
    have e1 := hS.eqn x t hx hxL ht (by linarith)
    have e2 := hS.eqn x (t + Δ) hx hxL (by linarith) (by linarith)
    have e3 : M'.Top = M.Top := rfl
    rw [e3]; linarith
  · intro t ht htT
    rw [hT'] at htT
    rw [hS.robin t ht (by linarith), hS.robin (t + Δ) (by linarith) (by linarith)]
    exact hf.antitone (show t ∈ Ici (0:ℝ) from ht.le) (show t + Δ ∈ Ici (0:ℝ) by
      simp only [mem_Ici]; linarith) (by linarith)
  · intro t ht htT
    rw [hT'] at htT
    rw [hS.right_bc t ht (by linarith), hS.right_bc (t + Δ) (by linarith) (by linarith)]
  · intro x hx hxL
    simp only [zero_add]
    rw [hS.initial x hx hxL]
    exact hge x Δ hx hxL hΔ hΔT.le
  · intro x t hx hxL ht htT
    rw [hT'] at htT
    exact hge x t hx hxL ht (by linarith)
  · intro x t hx hxL ht htT
    rw [hT'] at htT
    exact hge x (t + Δ) hx hxL (by linarith) (by linarith)

end DynReinsDiv.HJB.A4Aux

open DynReinsDiv.HJB.A4Aux in
theorem solution (M : Model) (L lam : ℝ) (hL : 0 < L) (hlam : 0 < lam)
    (hroot : M.fA lam = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ β fε : ℝ → ℝ, IsPenalty M ε β → IsRamp ε lam fε →
      ∀ u ux uxx ut : ℝ → ℝ → ℝ, IsC21RectClosed L M.T u ux uxx ut →
        SolvesPenalized M L lam β fε u ux uxx ut →
        (∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 1 ≤ u x t) →
        ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 0 ≤ ut x t ∧ ux x t ≤ 0 := by
  obtain ⟨ε₀, hε₀, h21⟩ := eq_A_21 M L lam hL hlam hroot
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεlt β fε hβ hf u ux uxx ut hC hS hge
  have h21' := h21 ε hε hεlt β fε hβ hf u ux uxx ut hC hS hge
  -- monotonicity in time
  have hmono : ∀ x : ℝ, 0 < x → x < L → ∀ s s' : ℝ, 0 < s → s < s' → s' ≤ M.T →
      u x s ≤ u x s' := by
    intro x hx hxL s s' hs hss hs'
    have := shift_le M L lam ε hL hlam hroot hε β fε hβ hf u ux uxx ut hC hS hge (s' - s)
      (by linarith) (by linarith) x s hx hxL hs (by linarith)
    rwa [show s + (s' - s) = s' by ring] at this
  have hlt : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t < M.T → 0 ≤ ut x t := by
    intro x t hx hxL ht htT
    have hd := hC.deriv_t x t hx hxL ht htT
    have hsl : Tendsto (slope (fun s => u x s) t) (𝓝[≠] t) (𝓝 (ut x t)) :=
      hasDerivAt_iff_tendsto_slope.1 hd
    have hsl' : Tendsto (slope (fun s => u x s) t) (𝓝[>] t) (𝓝 (ut x t)) :=
      hsl.mono_left (nhdsWithin_mono _ (fun s hs => ne_of_gt hs))
    refine ge_of_tendsto hsl' ?_
    filter_upwards [Ioo_mem_nhdsGT htT] with s hs
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.2 (hmono x hx hxL t s ht hs.1 hs.2.le)) (by linarith [hs.1])
  intro x t hx hxL ht htT
  refine ⟨?_, h21' x t hx hxL ht htT⟩
  rcases htT.lt_or_eq with htT' | htT'
  · exact hlt x t hx hxL ht htT'
  · subst htT'
    have hcont : ContinuousOn (fun s => ut x s) (Ioc 0 M.T) :=
      hC.cont_ut.comp (continuousOn_const.prodMk continuousOn_id) fun s hs =>
        ⟨⟨hx.le, hxL.le⟩, ⟨hs.1.le, hs.2⟩⟩
    have hmem : Ioc 0 M.T ∈ 𝓝[<] M.T :=
      mem_of_superset (Ioo_mem_nhdsLT ht) Ioo_subset_Ioc_self
    have hT : Tendsto (fun s => ut x s) (𝓝[<] M.T) (𝓝 (ut x M.T)) :=
      ((hcont M.T ⟨ht, le_rfl⟩).mono_of_mem_nhdsWithin hmem).tendsto
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    exact hlt x s hx hxL hs.1 hs.2
