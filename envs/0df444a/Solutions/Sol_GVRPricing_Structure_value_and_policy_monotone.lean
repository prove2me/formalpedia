-- Prove2me | solution 1 for GVRPricing.Structure.value_and_policy_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T23:54:00.277158+00:00
-- url     : https://prove2.me/submissions/ccca8690-7723-4dea-a69c-b8fc265153ee

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model
import Definitions.Def_GVRPricing_Structure_IsHJBSolution

set_option autoImplicit false

open GVRPricing.Structure in
theorem gvr1_sub (M : Model) : Set.Icc 0 M.lamStar ⊆ M.Λ :=
  M.ordConnected.out M.zero_mem M.lamStar_isLeast.1.1

open GVRPricing.Structure in
theorem gvr1_exA (M : Model) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    BddAbove (hamObjective M Δ '' M.Λ) ∧
    ∃ x ∈ Set.Icc 0 M.lamStar, IsMaxOn (hamObjective M Δ) M.Λ x := by
  have hls : M.lamStar ∈ M.Λ := M.lamStar_isLeast.1.1
  have hmax : ∀ y ∈ M.Λ, revRate M.p y ≤ revRate M.p M.lamStar := M.lamStar_isLeast.1.2
  have h0 : (0:ℝ) ≤ M.lamStar := M.subset_nonneg hls
  have hsub : Set.Icc 0 M.lamStar ⊆ M.Λ := M.ordConnected.out M.zero_mem hls
  have hcont : ContinuousOn (hamObjective M Δ) (Set.Icc 0 M.lamStar) := by
    have hr : ContinuousOn (revRate M.p) (Set.Icc 0 M.lamStar) := M.r_continuousOn.mono hsub
    unfold hamObjective Model.r
    exact hr.sub (continuousOn_id.mul continuousOn_const)
  obtain ⟨x, hx, hxmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 h0) hcont
  have hM : IsMaxOn (hamObjective M Δ) M.Λ x := by
    intro y hy
    rcases le_or_gt y M.lamStar with h | h
    · exact hxmax ⟨M.subset_nonneg hy, h⟩
    · have h1 : hamObjective M Δ y ≤ hamObjective M Δ M.lamStar := by
        unfold hamObjective Model.r
        have h2 := hmax y hy
        have h3 := mul_le_mul_of_nonneg_right h.le hΔ
        linarith
      exact h1.trans (hxmax ⟨h0, le_rfl⟩)
  have hG1 : IsGreatest (hamObjective M Δ '' M.Λ) (hamObjective M Δ x) :=
    ⟨Set.mem_image_of_mem _ (hsub hx), by rintro _ ⟨y, hy, rfl⟩; exact hM hy⟩
  exact ⟨hG1.bddAbove, x, hx, hM⟩

open GVRPricing.Structure in
theorem gvr1_h0 (M : Model) (Δ : ℝ) : hamObjective M Δ 0 = 0 := by
  simp [hamObjective, Model.r, revRate]

open GVRPricing.Structure in
theorem gvr1_psi_eq (M : Model) {Δ x : ℝ} (hx : x ∈ M.Λ)
    (hm : IsMaxOn (hamObjective M Δ) M.Λ x) :
    sSup (hamObjective M Δ '' M.Λ) = hamObjective M Δ x :=
  IsGreatest.csSup_eq ⟨Set.mem_image_of_mem _ hx, by rintro _ ⟨y, hy, rfl⟩; exact hm hy⟩

open GVRPricing.Structure in
theorem gvr1_psi_nonneg (M : Model) {a : ℝ} (hb : BddAbove (hamObjective M a '' M.Λ)) :
    0 ≤ sSup (hamObjective M a '' M.Λ) := by
  have := le_csSup hb (Set.mem_image_of_mem (hamObjective M a) M.zero_mem)
  rwa [gvr1_h0] at this

open GVRPricing.Structure in
theorem gvr1_psi_anti (M : Model) {a b : ℝ} (ha : BddAbove (hamObjective M a '' M.Λ))
    (hab : a ≤ b) :
    sSup (hamObjective M b '' M.Λ) ≤ sSup (hamObjective M a '' M.Λ) := by
  apply csSup_le (Set.Nonempty.image _ ⟨0, M.zero_mem⟩)
  rintro _ ⟨x, hx, rfl⟩
  have hx0 : (0:ℝ) ≤ x := M.subset_nonneg hx
  have h1 : hamObjective M b x ≤ hamObjective M a x := by
    unfold hamObjective
    nlinarith [mul_le_mul_of_nonneg_left hab hx0]
  exact h1.trans (le_csSup ha (Set.mem_image_of_mem _ hx))

open GVRPricing.Structure in
theorem gvr1_amax_pos (M : Model) {b x : ℝ}
    (hψ : 0 < sSup (hamObjective M b '' M.Λ)) (hx : x ∈ M.Λ)
    (hm : IsMaxOn (hamObjective M b) M.Λ x) : 0 < x := by
  have hx0 : (0:ℝ) ≤ x := M.subset_nonneg hx
  rcases hx0.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [gvr1_psi_eq M hx hm, ← h, gvr1_h0] at hψ
    exact lt_irrefl _ hψ

open GVRPricing.Structure in
theorem gvr1_psi_strict (M : Model) {a b : ℝ} (ha : BddAbove (hamObjective M a '' M.Λ))
    (hb : 0 ≤ b) (hψ : 0 < sSup (hamObjective M b '' M.Λ)) (hab : a < b) :
    sSup (hamObjective M b '' M.Λ) < sSup (hamObjective M a '' M.Λ) := by
  obtain ⟨-, x, hxI, hm⟩ := gvr1_exA M b hb
  have hxΛ := gvr1_sub M hxI
  have hx0 := gvr1_amax_pos M hψ hxΛ hm
  have h2 := le_csSup ha (Set.mem_image_of_mem (hamObjective M a) hxΛ)
  rw [gvr1_psi_eq M hxΛ hm]
  have : hamObjective M b x < hamObjective M a x := by
    unfold hamObjective
    nlinarith [mul_lt_mul_of_pos_left hab hx0]
  linarith

open GVRPricing.Structure in
theorem gvr1_psi_lip (M : Model) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    sSup (hamObjective M a '' M.Λ) ≤ sSup (hamObjective M b '' M.Λ) + M.lamStar * (b - a) := by
  obtain ⟨-, x, hxI, hm⟩ := gvr1_exA M a ha
  obtain ⟨hbb, -⟩ := gvr1_exA M b (ha.trans hab)
  have hxΛ := gvr1_sub M hxI
  rw [gvr1_psi_eq M hxΛ hm]
  have h2 := le_csSup hbb (Set.mem_image_of_mem (hamObjective M b) hxΛ)
  have h3 : x * (b - a) ≤ M.lamStar * (b - a) :=
    mul_le_mul_of_nonneg_right hxI.2 (sub_nonneg.2 hab)
  have : hamObjective M a x = hamObjective M b x + x * (b - a) := by
    unfold hamObjective; ring
  linarith

open GVRPricing.Structure in
theorem gvr1_lam_pos (M : Model) (hint : M.lamStar ∈ interior M.Λ) : 0 < M.lamStar := by
  have : M.lamStar ∈ interior (Set.Ici (0:ℝ)) := interior_mono M.subset_nonneg hint
  rwa [interior_Ici] at this

open GVRPricing.Structure in
theorem gvr1_psi0_pos (M : Model) (hint : M.lamStar ∈ interior M.Λ) :
    0 < sSup (hamObjective M 0 '' M.Λ) := by
  have hpos := gvr1_lam_pos M hint
  obtain ⟨hbd, -⟩ := gvr1_exA M 0 le_rfl
  have h1 := le_csSup hbd (Set.mem_image_of_mem (hamObjective M 0) M.lamStar_isLeast.1.1)
  have h2 : 0 < hamObjective M 0 M.lamStar := by
    by_contra hcon
    push_neg at hcon
    have h00 : revRate M.p 0 = 0 := by simp [revRate]
    have hcon' : revRate M.p M.lamStar ≤ 0 := by
      simpa [hamObjective, Model.r] using hcon
    have hmax0 : ∀ y ∈ M.Λ, revRate M.p y ≤ revRate M.p 0 := by
      intro y hy
      have := M.lamStar_isLeast.1.2 y hy
      linarith
    have : M.lamStar ≤ 0 := M.lamStar_isLeast.2 ⟨M.zero_mem, hmax0⟩
    linarith
  linarith

open GVRPricing.Structure in
theorem gvr1_mem_int (M : Model) (hint : M.lamStar ∈ interior M.Λ) {x : ℝ} (hx0 : 0 < x)
    (hxl : x ≤ M.lamStar) : x ∈ interior M.Λ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ hint
  have hd : dist (M.lamStar + ε / 2) M.lamStar = ε / 2 := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
  have hmem : M.lamStar + ε / 2 ∈ M.Λ :=
    interior_subset (hball (Metric.mem_ball.2 (by rw [hd]; linarith)))
  have hIcc : Set.Icc 0 (M.lamStar + ε / 2) ⊆ M.Λ := M.ordConnected.out M.zero_mem hmem
  exact interior_maximal (Set.Ioo_subset_Icc_self.trans hIcc) isOpen_Ioo ⟨hx0, by linarith⟩

open GVRPricing.Structure in
theorem gvr1_foc (M : Model) (hdiff : ∀ x ∈ interior M.Λ, DifferentiableAt ℝ M.r x)
    {a x : ℝ} (hx : x ∈ interior M.Λ) (hm : IsMaxOn (hamObjective M a) M.Λ x) :
    deriv M.r x = a := by
  have hloc : IsLocalMax (hamObjective M a) x := hm.isLocalMax (mem_interior_iff_mem_nhds.1 hx)
  have hd : HasDerivAt (hamObjective M a) (deriv M.r x - 1 * a) x :=
    (hdiff x hx).hasDerivAt.sub ((hasDerivAt_id' x).mul_const a)
  have := hloc.hasDerivAt_eq_zero hd
  linarith

open GVRPricing.Structure in
theorem gvr1_amax_strict (M : Model) (hdiff : ∀ x ∈ interior M.Λ, DifferentiableAt ℝ M.r x)
    (hint : M.lamStar ∈ interior M.Λ) {a b xa xb : ℝ} (hab : a < b)
    (hψb : 0 < sSup (hamObjective M b '' M.Λ))
    (hxa : xa ∈ Set.Icc 0 M.lamStar) (hma : IsMaxOn (hamObjective M a) M.Λ xa)
    (hxb : xb ∈ Set.Icc 0 M.lamStar) (hmb : IsMaxOn (hamObjective M b) M.Λ xb) : xb < xa := by
  have hle : xb ≤ xa := by
    have h1 : hamObjective M a xb ≤ hamObjective M a xa := hma (gvr1_sub M hxb)
    have h2 : hamObjective M b xa ≤ hamObjective M b xb := hmb (gvr1_sub M hxa)
    unfold hamObjective at h1 h2
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos (sub_pos.2 hcon) (sub_pos.2 hab)]
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have hxb0 := gvr1_amax_pos M hψb (gvr1_sub M hxb) hmb
    have hib := gvr1_mem_int M hint hxb0 hxb.2
    have hia : xa ∈ interior M.Λ := h ▸ hib
    have e1 := gvr1_foc M hdiff hia hma
    have e2 := gvr1_foc M hdiff hib hmb
    rw [h] at e2
    linarith

theorem gvr1_ns (f f' : ℝ → ℝ) (hc : ContinuousOn f (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt f (f' t) t) (h0 : 0 ≤ f 0)
    (hb : ∀ t, 0 < t → f t < 0 → 0 ≤ f' t) : ∀ t, 0 ≤ t → 0 ≤ f t := by
  intro s hs
  by_contra hneg
  push_neg at hneg
  have hs0 : 0 < s := lt_of_le_of_ne hs (by rintro rfl; linarith)
  have hAc : IsClosed (Set.Icc 0 s ∩ f ⁻¹' Set.Ici 0) :=
    (hc.mono Set.Icc_subset_Ici_self).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hAne : (Set.Icc 0 s ∩ f ⁻¹' Set.Ici 0).Nonempty := ⟨0, ⟨le_rfl, hs⟩, h0⟩
  have hAbd : BddAbove (Set.Icc 0 s ∩ f ⁻¹' Set.Ici 0) := ⟨s, fun x hx => hx.1.2⟩
  have hT := hAc.csSup_mem hAne hAbd
  have hfT : 0 ≤ f (sSup (Set.Icc 0 s ∩ f ⁻¹' Set.Ici 0)) := hT.2
  have hT0 : 0 ≤ sSup (Set.Icc 0 s ∩ f ⁻¹' Set.Ici 0) := hT.1.1
  have hTs : sSup (Set.Icc 0 s ∩ f ⁻¹' Set.Ici 0) < s := by
    rcases hT.1.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hfT; linarith
  have hneg' : ∀ u ∈ Set.Ioo (sSup (Set.Icc 0 s ∩ f ⁻¹' Set.Ici 0)) s, f u < 0 := by
    intro u hu
    by_contra h
    push_neg at h
    have : u ≤ sSup (Set.Icc 0 s ∩ f ⁻¹' Set.Ici 0) :=
      le_csSup hAbd ⟨⟨hT0.trans hu.1.le, hu.2.le⟩, h⟩
    linarith [hu.1]
  have hmono : MonotoneOn f (Set.Icc (sSup (Set.Icc 0 s ∩ f ⁻¹' Set.Ici 0)) s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ s) (hc.mono (fun x hx => le_trans hT0 hx.1))
    · rw [interior_Icc]
      intro u hu
      exact (hd u (lt_of_le_of_lt hT0 hu.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro u hu
      rw [(hd u (lt_of_le_of_lt hT0 hu.1)).deriv]
      exact hb u (lt_of_le_of_lt hT0 hu.1) (hneg' u hu)
  have := hmono ⟨le_rfl, hTs.le⟩ ⟨hTs.le, le_rfl⟩ hTs.le
  linarith

theorem gvr1_sp (f f' : ℝ → ℝ) (hc : ContinuousOn f (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt f (f' t) t) (h0 : f 0 = 0)
    (hb : ∀ t, 0 < t → f t ≤ 0 → 0 < f' t) : ∀ t, 0 < t → 0 < f t := by
  have hnn := gvr1_ns f f' hc hd h0.ge (fun t ht h => (hb t ht h.le).le)
  intro t ht
  by_contra hle
  push_neg at hle
  have hft : f t = 0 := le_antisymm hle (hnn t ht.le)
  have hmin : IsLocalMin f t := by
    filter_upwards [Ici_mem_nhds ht] with u hu
    rw [hft]
    exact hnn u hu
  have := hmin.hasDerivAt_eq_zero (hd t ht)
  linarith [hb t ht hle]

open GVRPricing.Structure in
theorem gvr1_gron (M : Model) (hint : M.lamStar ∈ interior M.Λ) (u : ℝ → ℝ)
    (hc : ContinuousOn u (Set.Ici 0)) (h0 : u 0 = 0)
    (hd : ∀ t, 0 < t → HasDerivAt u (sSup (hamObjective M (u t) '' M.Λ)) t)
    (hbd : ∀ t, 0 < t → BddAbove (hamObjective M (u t) '' M.Λ)) :
    ∀ t, 0 ≤ t → 0 < sSup (hamObjective M (u t) '' M.Λ) := by
  have hmono : MonotoneOn u (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hc
    · rw [interior_Ici]
      intro x hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      rw [(hd x hx).deriv]
      exact gvr1_psi_nonneg M (hbd x hx)
  have hnn : ∀ t, 0 ≤ t → 0 ≤ u t := by
    intro t ht
    have := hmono (Set.mem_Ici.2 (le_refl (0:ℝ))) ht ht
    rwa [h0] at this
  intro s hs
  by_contra hcon
  push_neg at hcon
  have hc0 := hnn s hs
  have hgm : MonotoneOn (fun t => (u s - u t) * Real.exp (M.lamStar * t)) (Set.Icc 0 s) := by
    have hD : ∀ x, 0 < x → HasDerivAt (fun t => (u s - u t) * Real.exp (M.lamStar * t))
        ((0 - sSup (hamObjective M (u x) '' M.Λ)) * Real.exp (M.lamStar * x) +
          (u s - u x) * (Real.exp (M.lamStar * x) * (M.lamStar * 1))) x := fun x hx =>
      ((hasDerivAt_const x (u s)).sub (hd x hx)).mul (((hasDerivAt_id' x).const_mul M.lamStar).exp)
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 s)
    · exact (continuousOn_const.sub (hc.mono Set.Icc_subset_Ici_self)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · rw [interior_Icc]
      intro x hx
      exact (hD x hx.1).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hD x hx.1).deriv]
      have hux : u x ≤ u s := hmono (le_of_lt hx.1 : (0:ℝ) ≤ x) hs hx.2.le
      have hlip := gvr1_psi_lip M (hnn x hx.1.le) hux
      have hE := Real.exp_pos (M.lamStar * x)
      have key : 0 ≤ -sSup (hamObjective M (u x) '' M.Λ) + (u s - u x) * M.lamStar := by
        nlinarith
      nlinarith [mul_nonneg key hE.le]
  have := hgm ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  simp only [h0, sub_zero, mul_zero, Real.exp_zero, mul_one, sub_self, zero_mul] at this
  have hc' : u s = 0 := le_antisymm this hc0
  rw [hc'] at hcon
  linarith [gvr1_psi0_pos M hint]

open GVRPricing.Structure in
theorem solution (M : Model) (hstrict : StrictConcaveOn ℝ M.Λ M.r)
    (hdiff : ∀ x ∈ interior M.Λ, DifferentiableAt ℝ M.r x)
    (hint : M.lamStar ∈ interior M.Λ)
    (J : ℕ → ℝ → ℝ) (hJ : IsHJBSolution M J) :
    (∀ t : ℝ, 0 < t → StrictMono (fun n : ℕ => J n t)) ∧
    (∀ n : ℕ, 1 ≤ n → StrictMonoOn (J n) (Set.Ici 0)) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t → J (n + 1) t - J n t < J n t - J (n - 1) t) ∧
    (∀ n : ℕ, 1 ≤ n → StrictConcaveOn ℝ (Set.Ici 0) (J n)) ∧
    ∃ ℓ : ℕ → ℝ → ℝ,
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t → IsOptimalIntensity M J n t (ℓ n t)) ∧
      (∀ t : ℝ, 0 < t → StrictMonoOn (fun n : ℕ => ℓ n t) (Set.Ici 1)) ∧
      (∀ n : ℕ, 1 ≤ n → StrictAntiOn (ℓ n) (Set.Ioi 0)) ∧
      (∀ t : ℝ, 0 < t → StrictAntiOn (fun n : ℕ => M.p (ℓ n t)) (Set.Ici 1)) ∧
      (∀ n : ℕ, 1 ≤ n → StrictMonoOn (fun t : ℝ => M.p (ℓ n t)) (Set.Ioi 0)) := by
  obtain ⟨hJ0, hJt0, hJc, hJd⟩ := hJ
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ → ℝ, ∀ k t, D k t = J (k + 1) t - J k t := ⟨_, fun _ _ => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ∀ x, ψ x = sSup (hamObjective M x '' M.Λ) := ⟨_, fun _ => rfl⟩
  have hDf : ∀ k, D k = fun t => J (k + 1) t - J k t := fun k => funext (hD k)
  have hJ0d : ∀ t, 0 < t → HasDerivAt (J 0) 0 t := fun t ht =>
    (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq
      (by filter_upwards [Ici_mem_nhds ht] with u hu using hJ0 u hu)
  have hJd' : ∀ k t, 0 < t → BddAbove (hamObjective M (D k t) '' M.Λ) ∧
      HasDerivAt (J (k + 1)) (ψ (D k t)) t := by
    intro k t ht
    have h := hJd (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) t ht
    rw [Nat.add_sub_cancel] at h
    rw [hD, hψ]
    exact h
  have hDc : ∀ k, ContinuousOn (D k) (Set.Ici 0) := fun k => by
    rw [hDf]; exact (hJc _).sub (hJc _)
  have hD0 : ∀ k, D k 0 = 0 := fun k => by rw [hD, hJt0, hJt0, sub_zero]
  have hDbd : ∀ k t, 0 < t → BddAbove (hamObjective M (D k t) '' M.Λ) :=
    fun k t ht => (hJd' k t ht).1
  have hD0d : ∀ t, 0 < t → HasDerivAt (D 0) (ψ (D 0 t)) t := by
    intro t ht
    have h := (hJd' 0 t ht).2.sub (hJ0d t ht)
    rw [sub_zero] at h
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => hD 0 x))
  have hDSd : ∀ k t, 0 < t → HasDerivAt (D (k + 1)) (ψ (D (k + 1) t) - ψ (D k t)) t := by
    intro k t ht
    have h := (hJd' (k + 1) t ht).2.sub (hJd' k t ht).2
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => hD (k + 1) x))
  have hP1 : ∀ a b, BddAbove (hamObjective M a '' M.Λ) → a ≤ b → ψ b ≤ ψ a := by
    intro a b ha hab; rw [hψ, hψ]; exact gvr1_psi_anti M ha hab
  have hP2 : ∀ a b, BddAbove (hamObjective M a '' M.Λ) → 0 ≤ b → 0 < ψ b → a < b →
      ψ b < ψ a := by
    intro a b ha hb hψb hab; rw [hψ] at hψb; rw [hψ, hψ]; exact gvr1_psi_strict M ha hb hψb hab
  have hψ0 : 0 < ψ 0 := by rw [hψ]; exact gvr1_psi0_pos M hint
  -- main induction
  have hmain : ∀ k, ((∀ t, 0 < t → 0 < D k t) ∧ (∀ t, 0 ≤ t → 0 < ψ (D k t))) ∧
      (∀ t, 0 < t → D (k + 1) t < D k t) := by
    -- the R-step from P(k) and the bracket positivity
    have hR : ∀ k, (∀ t, 0 ≤ t → 0 < ψ (D k t)) →
        (∀ t, 0 < t → HasDerivAt (D k) (ψ (D k t) - (if k = 0 then 0 else ψ (D (k - 1) t))) t) →
        (∀ t, 0 < t → 0 < ψ (D k t) - (if k = 0 then 0 else ψ (D (k - 1) t))) →
        ∀ t, 0 < t → D (k + 1) t < D k t := by
      intro k hpos hdk hbr
      have hsp := gvr1_sp (fun t => D k t - D (k + 1) t)
        (fun t => (ψ (D k t) - (if k = 0 then 0 else ψ (D (k - 1) t))) -
          (ψ (D (k + 1) t) - ψ (D k t)))
        ((hDc k).sub (hDc (k + 1)))
        (fun t ht => (hdk t ht).sub (hDSd k t ht))
        (by simp only [hD0, sub_self])
        (by
          intro t ht hle
          have hle' : D k t - D (k + 1) t ≤ 0 := hle
          have h1 : ψ (D (k + 1) t) ≤ ψ (D k t) := hP1 _ _ (hDbd k t ht) (by linarith)
          have h2 := hbr t ht
          show 0 < (ψ (D k t) - (if k = 0 then 0 else ψ (D (k - 1) t))) -
            (ψ (D (k + 1) t) - ψ (D k t))
          linarith)
      intro t ht
      have : 0 < D k t - D (k + 1) t := hsp t ht
      linarith
    intro k
    induction k with
    | zero =>
      have hpsi : ∀ t, 0 ≤ t → 0 < ψ (D 0 t) := by
        intro t ht
        rw [hψ]
        exact gvr1_gron M hint (D 0) (hDc 0) (hD0 0)
          (fun t ht => by rw [← hψ]; exact hD0d t ht) (hDbd 0) t ht
      have hposD : ∀ t, 0 < t → 0 < D 0 t :=
        gvr1_sp (D 0) (fun t => ψ (D 0 t)) (hDc 0) hD0d (hD0 0)
          (fun t ht _ => hpsi t ht.le)
      refine ⟨⟨hposD, hpsi⟩, hR 0 hpsi ?_ ?_⟩
      · intro t ht; rw [if_pos rfl, sub_zero]; exact hD0d t ht
      · intro t ht; rw [if_pos rfl, sub_zero]; exact hpsi t ht.le
    | succ k ih =>
      obtain ⟨⟨hposk, hpsik⟩, hRk⟩ := ih
      have hposD : ∀ t, 0 < t → 0 < D (k + 1) t := by
        apply gvr1_sp (D (k + 1)) (fun t => ψ (D (k + 1) t) - ψ (D k t)) (hDc _)
          (hDSd k) (hD0 _)
        intro t ht hle
        have := hP2 (D (k + 1) t) (D k t) (hDbd _ t ht) (hposk t ht).le (hpsik t ht.le)
          (lt_of_le_of_lt hle (hposk t ht))
        show 0 < ψ (D (k + 1) t) - ψ (D k t)
        linarith
      have hpsi : ∀ t, 0 ≤ t → 0 < ψ (D (k + 1) t) := by
        intro t ht
        rcases ht.lt_or_eq with ht | ht
        · exact lt_of_lt_of_le (hpsik t ht.le) (hP1 _ _ (hDbd _ t ht) (hRk t ht).le)
        · rw [← ht, hD0]; exact hψ0
      refine ⟨⟨hposD, hpsi⟩, hR (k + 1) hpsi ?_ ?_⟩
      · intro t ht
        rw [if_neg (Nat.add_one_ne_zero k), Nat.add_sub_cancel]
        exact hDSd k t ht
      · intro t ht
        rw [if_neg (Nat.add_one_ne_zero k), Nat.add_sub_cancel]
        have := hP2 (D (k + 1) t) (D k t) (hDbd _ t ht) (hposk t ht).le (hpsik t ht.le)
          (hRk t ht)
        linarith
  have hpos : ∀ k t, 0 < t → 0 < D k t := fun k => (hmain k).1.1
  have hpsi : ∀ k t, 0 ≤ t → 0 < ψ (D k t) := fun k => (hmain k).1.2
  have hRR : ∀ k t, 0 < t → D (k + 1) t < D k t := fun k => (hmain k).2
  have hnn : ∀ k t, 0 ≤ t → 0 ≤ D k t := by
    intro k t ht
    rcases ht.lt_or_eq with ht | ht
    · exact (hpos k t ht).le
    · rw [← ht, hD0]
  -- D k strictly increasing in t
  have hmonoD : ∀ k, StrictMonoOn (D k) (Set.Ici 0) := by
    intro k
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (hDc k)
    rw [interior_Ici]
    intro x hx
    cases k with
    | zero => rw [(hD0d x hx).deriv]; exact hpsi 0 x hx.le
    | succ j =>
      rw [(hDSd j x hx).deriv]
      have := hP2 (D (j + 1) x) (D j x) (hDbd _ x hx) (hnn j x hx.le) (hpsi j x hx.le)
        (hRR j x hx)
      linarith
  -- index form
  have hidx : ∀ n : ℕ, 1 ≤ n → ∃ k, n = k + 1 := fun n hn => Nat.exists_eq_add_of_le' hn
  have hDn : ∀ k t, J (k + 1) t - J (k + 1 - 1) t = D k t := by
    intro k t; rw [Nat.add_sub_cancel, hD]
  -- argmax choice
  have hex : ∀ x : ℝ, ∃ y : ℝ, 0 ≤ x →
      y ∈ Set.Icc 0 M.lamStar ∧ IsMaxOn (hamObjective M x) M.Λ y := by
    intro x
    by_cases hx : 0 ≤ x
    · obtain ⟨-, y, hy, hm⟩ := gvr1_exA M x hx
      exact ⟨y, fun _ => ⟨hy, hm⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose am ham using hex
  have hamstrict : ∀ a b, 0 ≤ a → a < b → 0 < ψ b → am b < am a := by
    intro a b ha hab hψb
    rw [hψ] at hψb
    exact gvr1_amax_strict M hdiff hint hab hψb (ham a ha).1 (ham a ha).2
      (ham b (ha.trans hab.le)).1 (ham b (ha.trans hab.le)).2
  have hampos : ∀ b, 0 ≤ b → 0 < ψ b → 0 < am b := by
    intro b hb hψb
    rw [hψ] at hψb
    exact gvr1_amax_pos M hψb (gvr1_sub M (ham b hb).1) (ham b hb).2
  have hDanti : ∀ t, 0 < t → StrictAnti (fun k => D k t) :=
    fun t ht => strictAnti_nat_of_succ_lt (fun k => hRR k t ht)
  refine ⟨?_, ?_, ?_, ?_, fun n t => am (J n t - J (n - 1) t), ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    apply strictMono_nat_of_lt_succ
    intro k
    have := hpos k t ht
    rw [hD] at this
    show J k t < J (k + 1) t
    linarith
  · intro n hn
    obtain ⟨k, rfl⟩ := hidx n hn
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (hJc _)
    rw [interior_Ici]
    intro x hx
    rw [(hJd' k x hx).2.deriv]
    exact hpsi k x hx.le
  · intro n hn t ht
    obtain ⟨k, rfl⟩ := hidx n hn
    rw [Nat.add_sub_cancel]
    have := hRR k t ht
    rw [hD, hD] at this
    exact this
  · intro n hn
    obtain ⟨k, rfl⟩ := hidx n hn
    apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) (hJc _)
    rw [interior_Ici]
    intro x hx y hy hxy
    rw [(hJd' k x hx).2.deriv, (hJd' k y hy).2.deriv]
    exact hP2 _ _ (hDbd k x hx) (hnn k y (le_of_lt hy)) (hpsi k y (le_of_lt hy))
      (hmonoD k (le_of_lt hx : (0:ℝ) ≤ x) (le_of_lt hy : (0:ℝ) ≤ y) hxy)
  · intro n hn t ht
    obtain ⟨k, rfl⟩ := hidx n hn
    have h := ham (J (k + 1) t - J (k + 1 - 1) t) (by rw [hDn]; exact hnn k t ht.le)
    unfold IsOptimalIntensity
    exact ⟨gvr1_sub M h.1, h.2⟩
  · intro t ht m hm n hn hmn
    obtain ⟨i, rfl⟩ := hidx m hm
    obtain ⟨j, rfl⟩ := hidx n hn
    simp only [hDn]
    exact hamstrict _ _ (hnn j t ht.le) (hDanti t ht (by omega)) (hpsi i t ht.le)
  · intro n hn x hx y hy hxy
    obtain ⟨k, rfl⟩ := hidx n hn
    simp only [hDn]
    exact hamstrict _ _ (hnn k x (le_of_lt hx)) (hmonoD k (le_of_lt hx : (0:ℝ) ≤ x)
      (le_of_lt hy : (0:ℝ) ≤ y) hxy) (hpsi k y (le_of_lt hy))
  · intro t ht m hm n hn hmn
    obtain ⟨i, rfl⟩ := hidx m hm
    obtain ⟨j, rfl⟩ := hidx n hn
    simp only [hDn]
    have hlt := hamstrict _ _ (hnn j t ht.le) (hDanti t ht (by omega)) (hpsi i t ht.le)
    have hmi : am (D i t) ∈ M.Λ \ {0} :=
      ⟨gvr1_sub M (ham _ (hnn i t ht.le)).1,
        (hampos _ (hnn i t ht.le) (hpsi i t ht.le)).ne'⟩
    have hmj : am (D j t) ∈ M.Λ \ {0} :=
      ⟨gvr1_sub M (ham _ (hnn j t ht.le)).1,
        (hampos _ (hnn j t ht.le) (hpsi j t ht.le)).ne'⟩
    exact M.p_strictAntiOn hmi hmj hlt
  · intro n hn x hx y hy hxy
    obtain ⟨k, rfl⟩ := hidx n hn
    simp only [hDn]
    have hlt := hamstrict _ _ (hnn k x (le_of_lt hx)) (hmonoD k (le_of_lt hx : (0:ℝ) ≤ x)
      (le_of_lt hy : (0:ℝ) ≤ y) hxy) (hpsi k y (le_of_lt hy))
    have hmx : am (D k x) ∈ M.Λ \ {0} :=
      ⟨gvr1_sub M (ham _ (hnn k x (le_of_lt hx))).1,
        (hampos _ (hnn k x (le_of_lt hx)) (hpsi k x (le_of_lt hx))).ne'⟩
    have hmy : am (D k y) ∈ M.Λ \ {0} :=
      ⟨gvr1_sub M (ham _ (hnn k y (le_of_lt hy))).1,
        (hampos _ (hnn k y (le_of_lt hy)) (hpsi k y (le_of_lt hy))).ne'⟩
    exact M.p_strictAntiOn hmy hmx hlt
