-- Prove2me | solution 1 for DynReinsDiv.HJB.lemma_A_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:54:42.357138+00:00
-- url     : https://prove2.me/submissions/afe5db08-b010-459b-b251-2bd282ca9ca7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model
import Definitions.Def_DynReinsDiv_HJB_PDE
import Theorems.Thm_DynReinsDiv_HJB_eq_A_7_A_9
import Theorems.Thm_DynReinsDiv_HJB_lemma_A_4

open DynReinsDiv.HJB Set Filter Topology

namespace DynReinsDiv.HJB.A5Aux

/-- One-dimensional core of Lemma A.5 at a fixed time. -/
theorem core (M : Model) (lam : ℝ) (hlam : 0 < lam) (hroot : M.fA lam = 0) (L : ℝ)
    (β : ℝ → ℝ) (hβmono : Monotone β) (hβ0 : β 0 = -M.c) (hβc : Continuous β)
    (U V W Ut : ℝ → ℝ)
    (hUc : ContinuousOn U (Icc 0 L)) (hVc : ContinuousOn V (Icc 0 L))
    (hU' : ∀ x ∈ Ioo 0 L, HasDerivAt U (V x) x) (hV' : ∀ x ∈ Ioo 0 L, HasDerivAt V (W x) x)
    (heq : ∀ x ∈ Ioo 0 L, Ut x - M.Top (W x) (V x) (U x) + β (U x - 1) = 0)
    (hUt : ∀ x ∈ Ioo 0 L, 0 ≤ Ut x) (hU1 : ∀ x ∈ Ioo 0 L, 1 ≤ U x)
    (h0 : 0 ≤ lam * U 0 + V 0) : ∀ x ∈ Ioo 0 L, 0 ≤ lam * U x + V x := by
  obtain ⟨hAanti, hBanti, ⟨KA, hAl⟩, ⟨KB, hBl⟩, hbd, -, -⟩ := eq_A_7_A_9 M
  have hApos : ∀ y, 0 < M.A y := by
    intro y
    rcases lt_or_ge 0 y with hy | hy
    · exact (hbd y hy).1
    · exact lt_of_lt_of_le (hbd 1 one_pos).1 (hAanti (hy.trans zero_le_one))
  have hAc : Continuous M.A := hAl.continuous
  have hBc : Continuous M.B := hBl.continuous
  have hf0 : M.γ - M.B lam = -lam * M.A lam := by unfold Model.fA at hroot; linarith
  intro x0 hx0
  by_contra hneg
  push Not at hneg
  set g : ℝ → ℝ := fun x => lam * U x + V x with hg
  have hgc : ContinuousOn g (Icc 0 L) := (continuousOn_const.mul hUc).add hVc
  have hsub0 : Icc 0 x0 ⊆ Icc 0 L := Icc_subset_Icc le_rfl hx0.2.le
  set S : Set ℝ := Icc 0 x0 ∩ g ⁻¹' Ici 0 with hS
  have hSc : IsClosed S := (hgc.mono hsub0).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have h0S : (0:ℝ) ∈ S := ⟨⟨le_rfl, hx0.1.le⟩, h0⟩
  have hSb : BddAbove S := ⟨x0, fun x hx => hx.1.2⟩
  set x1 := sSup S with hx1
  have hx1S : x1 ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hSb
  have hx1nn : 0 ≤ x1 := hx1S.1.1
  have hx1lt : x1 < x0 := by
    rcases hx1S.1.2.lt_or_eq with h | h
    · exact h
    · exfalso; have := hx1S.2; rw [h] at this; simp only [mem_preimage, mem_Ici] at this
      linarith
  have hnegOn : ∀ x ∈ Ioc x1 x0, g x < 0 := by
    intro x hx
    by_contra hc; push Not at hc
    have : x ∈ S := ⟨⟨hx1nn.trans hx.1.le, hx.2⟩, hc⟩
    have := le_csSup hSb this
    linarith [hx.1]
  have hIoo : Ioo x1 x0 ⊆ Ioo 0 L := fun x hx => ⟨lt_of_le_of_lt hx1nn hx.1, hx.2.trans hx0.2⟩
  have hx1L : x1 ∈ Icc 0 L := ⟨hx1nn, (hx1lt.trans hx0.2).le⟩
  have hmemL : Icc 0 L ∈ 𝓝[>] x1 :=
    mem_of_superset (Ioo_mem_nhdsGT hx1lt) (fun x hx => Ioo_subset_Icc_self (hIoo hx))
  have hgx1 : g x1 ≤ 0 := by
    have ht : Tendsto g (𝓝[>] x1) (𝓝 (g x1)) :=
      ((hgc x1 hx1L).mono_of_mem_nhdsWithin hmemL).tendsto
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hx1lt] with x hx
    exact (hnegOn x ⟨hx.1, hx.2.le⟩).le
  have hgx1' : g x1 = 0 := le_antisymm hgx1 hx1S.2
  -- U is strictly decreasing on [x1, x0]
  have hVneg : ∀ x ∈ Ioo x1 x0, V x < 0 := by
    intro x hx
    have h1 := hnegOn x ⟨hx.1, hx.2.le⟩
    have h2 := hU1 x (hIoo hx)
    simp only [hg] at h1; nlinarith
  have hUanti : StrictAntiOn U (Icc x1 x0) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (hUc.mono (Icc_subset_Icc hx1nn hx0.2.le))
      fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hU' x (hIoo hx)).deriv]; exact hVneg x hx
  have hU0x : 1 ≤ U x0 := hU1 x0 hx0
  have hUx1 : 1 < U x1 :=
    lt_of_le_of_lt hU0x (hUanti ⟨le_rfl, hx1lt.le⟩ ⟨hx1lt.le, le_rfl⟩ hx1lt)
  have hUx1' : U x1 ≠ 0 := by linarith
  have hP : 0 < M.c * U x1 + β (U x1 - 1) := by
    have := hβmono (show (0:ℝ) ≤ U x1 - 1 by linarith)
    rw [hβ0] at this
    have := M.c_pos
    nlinarith
  have hVx1 : V x1 = -lam * U x1 := by simp only [hg] at hgx1'; linarith
  have hy1 : -V x1 / U x1 = lam := by rw [hVx1]; field_simp
  set R : ℝ → ℝ := fun x => lam * V x + ((M.γ - M.B (-V x / U x)) * V x +
    (M.c * U x + β (U x - 1))) / M.A (-V x / U x) with hR
  have hRx1 : 0 < R x1 := by
    simp only [hR]
    rw [hy1, hf0]
    have hA := hApos lam
    have e : (-lam * M.A lam * V x1 + (M.c * U x1 + β (U x1 - 1))) / M.A lam =
        -lam * V x1 + (M.c * U x1 + β (U x1 - 1)) / M.A lam := by
      field_simp
    rw [e]
    have := div_pos hP hA
    linarith
  have hRc : ContinuousWithinAt R (Icc 0 L) x1 := by
    have cU := hUc x1 hx1L
    have cV := hVc x1 hx1L
    have cy : ContinuousWithinAt (fun x => -V x / U x) (Icc 0 L) x1 := cV.neg.div cU hUx1'
    have cA : ContinuousWithinAt (fun x => M.A (-V x / U x)) (Icc 0 L) x1 :=
      hAc.continuousAt.comp_continuousWithinAt cy
    have cB : ContinuousWithinAt (fun x => M.B (-V x / U x)) (Icc 0 L) x1 :=
      hBc.continuousAt.comp_continuousWithinAt cy
    have cβ : ContinuousWithinAt (fun x => β (U x - 1)) (Icc 0 L) x1 :=
      hβc.continuousAt.comp_continuousWithinAt (cU.sub continuousWithinAt_const)
    exact (continuousWithinAt_const.mul cV).add
      ((((continuousWithinAt_const.sub cB).mul cV).add
        ((continuousWithinAt_const.mul cU).add cβ)).div cA (hApos _).ne')
  have hev : ∀ᶠ x in 𝓝[>] x1, 0 < R x ∧ x ∈ Ioo x1 x0 :=
    (((hRc.mono_of_mem_nhdsWithin hmemL).tendsto).eventually (lt_mem_nhds hRx1)).and
      (Ioo_mem_nhdsGT hx1lt)
  obtain ⟨b, hb, hbsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  set c := min b x0 with hc
  have hx1c : x1 < c := lt_min hb hx1lt
  have hcx0 : c ≤ x0 := min_le_right _ _
  have hgmono : StrictMonoOn g (Icc x1 c) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hgc.mono (Icc_subset_Icc hx1nn ((hcx0.trans hx0.2.le)))) fun x hx => ?_
    rw [interior_Icc] at hx
    have hxb : x ∈ Ioo x1 b := ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
    obtain ⟨hRpos, hxx0⟩ := hbsub hxb
    have hxL := hIoo hxx0
    have hd : HasDerivAt g (lam * V x + W x) x := ((hU' x hxL).const_mul lam).add (hV' x hxL)
    rw [hd.deriv]
    have he := heq x hxL
    unfold Model.Top at he
    have hA := hApos (-V x / U x)
    have hW : ((M.γ - M.B (-V x / U x)) * V x + (M.c * U x + β (U x - 1))) /
        M.A (-V x / U x) ≤ W x := by
      rw [div_le_iff₀ hA]
      have := hUt x hxL
      nlinarith
    simp only [hR] at hRpos
    linarith
  have hmid : (x1 + c) / 2 ∈ Ioo x1 c := ⟨by linarith, by linarith⟩
  have h1 := hgmono ⟨le_rfl, hx1c.le⟩ (Ioo_subset_Icc_self hmid) hmid.1
  have h2 := hnegOn ((x1 + c) / 2) ⟨hmid.1, hmid.2.le.trans hcx0⟩
  linarith

end DynReinsDiv.HJB.A5Aux

open DynReinsDiv.HJB.A5Aux in
theorem solution (M : Model) (L lam : ℝ) (hL : 0 < L) (hlam : 0 < lam)
    (hroot : M.fA lam = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ β fε : ℝ → ℝ, IsPenalty M ε β → IsRamp ε lam fε →
      ∀ u ux uxx ut : ℝ → ℝ → ℝ, IsC21RectClosed L M.T u ux uxx ut →
        SolvesPenalized M L lam β fε u ux uxx ut →
        (∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 1 ≤ u x t) →
        ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 0 ≤ lam * u x t + ux x t := by
  obtain ⟨ε₄, hε₄, h4⟩ := lemma_A_4 M L lam hL hlam hroot
  refine ⟨ε₄, hε₄, ?_⟩
  intro ε hε hεlt β fε hβ hf u ux uxx ut hC hS hge
  have hβmono : Monotone β :=
    monotone_of_deriv_nonneg (hβ.smooth.differentiable (by norm_num)) hβ.deriv_nonneg
  have hβc : Continuous β := hβ.smooth.continuous
  have h4' := h4 ε hε hεlt β fε hβ hf u ux uxx ut hC hS hge
  -- the ramp is nonnegative
  have hfnn : ∀ t : ℝ, 0 < t → 0 ≤ fε t := by
    intro t ht
    have h1 := hf.antitone (show t ∈ Ici (0:ℝ) from ht.le)
      (show max t ε ∈ Ici (0:ℝ) from le_max_of_le_left ht.le) (le_max_left t ε)
    rw [hf.vanish _ (le_max_right t ε)] at h1
    exact h1
  -- slices are continuous in x
  have slice : ∀ t ∈ Icc 0 M.T, ∀ f : ℝ → ℝ → ℝ,
      ContinuousOn (Function.uncurry f) (Icc 0 L ×ˢ Icc 0 M.T) →
      ContinuousOn (fun x => f x t) (Icc 0 L) := by
    intro t ht f hf
    exact hf.comp (continuousOn_id.prodMk continuousOn_const) fun x hx => ⟨hx, ht⟩
  -- the case t < T
  have hlt : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t < M.T → 0 ≤ lam * u x t + ux x t := by
    intro x t hx hxL ht htT
    have htI : t ∈ Icc 0 M.T := ⟨ht.le, htT.le⟩
    refine core M lam hlam hroot L β hβmono hβ.at_zero hβc (fun x => u x t) (fun x => ux x t)
      (fun x => uxx x t) (fun x => ut x t) (slice t htI u hC.cont) (slice t htI ux hC.cont_ux)
      (fun y hy => hC.deriv_x y t hy.1 hy.2 ht htT) (fun y hy => hC.deriv_xx y t hy.1 hy.2 ht htT)
      (fun y hy => hS.eqn y t hy.1 hy.2 ht htT.le) (fun y hy => (h4' y t hy.1 hy.2 ht htT.le).1)
      (fun y hy => hge y t hy.1 hy.2 ht htT.le) ?_ x ⟨hx, hxL⟩
    rw [hS.robin t ht htT.le]; exact hfnn t ht
  intro x t hx hxL ht htT
  rcases htT.lt_or_eq with htT' | htT'
  · exact hlt x t hx hxL ht htT'
  · -- t = T: pass to the limit s ↑ T
    subst htT'
    have hxI : x ∈ Icc 0 L := ⟨hx.le, hxL.le⟩
    have hcont : ContinuousOn (fun s => lam * u x s + ux x s) (Icc 0 M.T) := by
      have c1 : ContinuousOn (fun s => u x s) (Icc 0 M.T) :=
        hC.cont.comp (continuousOn_const.prodMk continuousOn_id) fun s hs => ⟨hxI, hs⟩
      have c2 : ContinuousOn (fun s => ux x s) (Icc 0 M.T) :=
        hC.cont_ux.comp (continuousOn_const.prodMk continuousOn_id) fun s hs => ⟨hxI, hs⟩
      exact (continuousOn_const.mul c1).add c2
    have hmem : Icc 0 M.T ∈ 𝓝[<] M.T :=
      mem_of_superset (Ioo_mem_nhdsLT ht) Ioo_subset_Icc_self
    have hT : Tendsto (fun s => lam * u x s + ux x s) (𝓝[<] M.T)
        (𝓝 (lam * u x M.T + ux x M.T)) :=
      ((hcont M.T ⟨ht.le, le_rfl⟩).mono_of_mem_nhdsWithin hmem).tendsto
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    exact hlt x s hx hxL hs.1 hs.2
