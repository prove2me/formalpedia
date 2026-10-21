-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.lemma_12_analytic
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:52:08.09909+00:00
-- url     : https://prove2.me/submissions/0bf7743d-b863-4fb8-bc18-2932959cafd3

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model

open Set Filter Topology

namespace DriftVarCtrl.FixedLB

lemma dv_mu_pos (p : Params) (c : Ctrl) : 0 < p.mu c := by
  cases c
  · exact p.hμ₁
  · exact p.hμ₂

lemma dv_sig_pos (p : Params) (c : Ctrl) : 0 < p.sig c := by
  cases c
  · exact p.hσ₁
  · exact p.hσ₂

/-- Every point of `(0, U)` that is not a breakpoint lies in an open piece. -/
lemma dv_mem_piece (p : Params) (π : IntervalPolicy p) (x : ℝ) (hx : x ∈ Ioo 0 p.U)
    (hxS : x ∉ Set.range π.S) :
    ∃ j : Fin π.k, x ∈ Ioo (π.S j.castSucc) (π.S j.succ) := by
  classical
  set s := Finset.univ.filter (fun i : Fin (π.k + 1) => π.S i < x) with hs
  have h0 : (0 : Fin (π.k + 1)) ∈ s := by
    simp [hs, π.S_zero, hx.1]
  have hne : s.Nonempty := ⟨_, h0⟩
  set i₀ := s.max' hne with hi₀
  have hi₀s : i₀ ∈ s := s.max'_mem hne
  have hi₀x : π.S i₀ < x := by simpa [hs] using hi₀s
  have hlt : i₀.val < π.k := by
    by_contra hcon
    have : i₀ = Fin.last π.k := by
      ext; simp; omega
    rw [this, π.S_last] at hi₀x
    linarith [hx.2]
  refine ⟨⟨i₀.val, hlt⟩, ?_, ?_⟩
  · have : (⟨i₀.val, hlt⟩ : Fin π.k).castSucc = i₀ := by ext; simp
    rw [this]; exact hi₀x
  · rcases lt_trichotomy (π.S (⟨i₀.val, hlt⟩ : Fin π.k).succ) x with h | h | h
    · exfalso
      have hmem : (⟨i₀.val, hlt⟩ : Fin π.k).succ ∈ s := by simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
      have := s.le_max' _ hmem
      rw [← hi₀] at this
      have : ((⟨i₀.val, hlt⟩ : Fin π.k).succ).val ≤ i₀.val := this
      simp at this
    · exact absurd ⟨_, h⟩ hxS
    · exact h

theorem lemma_12_analytic_proof (p : Params) (V : ℝ → ℝ) (E : Finset ℝ)
    (hV1 : ContDiffOn ℝ 1 V (Set.Icc 0 p.U))
    (hV2 : ∀ x ∈ Set.Ioo 0 p.U, x ∉ E → ContDiffAt ℝ 2 V x)
    (h0 : V 0 = 0) (hUM : V p.U = p.M)
    (hHJB : ∀ x ∈ Set.Ioo 0 p.U, x ∉ E → ∀ c : Ctrl,
      0 ≤ p.cost c + p.mu c * deriv V x + p.sig c ^ 2 / 2 * deriv (deriv V) x)
    (π : IntervalPolicy p) (W : ℝ → ℝ) (hW : IsValue p π W) :
    ∀ x ∈ Set.Icc 0 p.U, V x ≤ W x := by
  classical
  obtain ⟨hW1, hW0, hWU, hWode⟩ := hW
  set ψ : ℝ → ℝ := fun x => deriv W x - deriv V x with hψ
  set D : ℝ → ℝ := fun x => W x - V x with hD
  have hV1o : ContDiffOn ℝ 1 V (Ioo 0 p.U) := hV1.mono Ioo_subset_Icc_self
  have hW1o : ContDiffOn ℝ 1 W (Ioo 0 p.U) := hW1.mono Ioo_subset_Icc_self
  have hVd : ∀ x ∈ Ioo 0 p.U, DifferentiableAt ℝ V x := fun x hx =>
    ((hV1o.differentiableOn one_ne_zero) x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hWd : ∀ x ∈ Ioo 0 p.U, DifferentiableAt ℝ W x := fun x hx =>
    ((hW1o.differentiableOn one_ne_zero) x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hψc : ContinuousOn ψ (Ioo 0 p.U) :=
    (hW1o.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).sub
      (hV1o.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl)
  have hDc : ContinuousOn D (Icc 0 p.U) := hW1.continuousOn.sub hV1.continuousOn
  -- the bad finite set
  set B : Finset ℝ := E ∪ Finset.univ.image π.S with hB
  -- local differential inequality
  have hloc : ∀ x ∈ Ioo 0 p.U, x ∉ B →
      HasDerivAt ψ (deriv (deriv W) x - deriv (deriv V) x) x ∧
      (0 < ψ x → deriv (deriv W) x - deriv (deriv V) x < 0) := by
    intro x hx hxB
    have hxE : x ∉ E := fun h => hxB (by simp [hB, h])
    have hxS : x ∉ Set.range π.S := by
      rintro ⟨i, rfl⟩; exact hxB (by simp [hB])
    obtain ⟨j, hj⟩ := dv_mem_piece p π x hx hxS
    obtain ⟨hW2, hode⟩ := hWode j x hj
    have hV2x := hV2 x hx hxE
    have hdW : DifferentiableAt ℝ (deriv W) x :=
      (hW2.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hdV : DifferentiableAt ℝ (deriv V) x :=
      (hV2x.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    refine ⟨hdW.hasDerivAt.sub hdV.hasDerivAt, ?_⟩
    intro hpos
    have hH := hHJB x hx hxE (π.ctrl j)
    have hmu := dv_mu_pos p (π.ctrl j)
    have hsig := dv_sig_pos p (π.ctrl j)
    have hsig2 : 0 < p.sig (π.ctrl j) ^ 2 / 2 := by positivity
    have hψx : ψ x = deriv W x - deriv V x := rfl
    have key : p.mu (π.ctrl j) * ψ x +
        p.sig (π.ctrl j) ^ 2 / 2 * (deriv (deriv W) x - deriv (deriv V) x) ≤ 0 := by
      rw [hψx]; nlinarith
    by_contra hcon
    push Not at hcon
    have : 0 < p.mu (π.ctrl j) * ψ x := mul_pos hmu hpos
    nlinarith [mul_nonneg hsig2.le hcon]
  -- propagation of nonpositivity of ψ
  have hprop : ∀ ξ ∈ Ioo 0 p.U, ψ ξ ≤ 0 → ∀ y ∈ Ioo 0 p.U, ξ ≤ y → ψ y ≤ 0 := by
    intro ξ hξ hψξ y hy hξy
    by_contra hcon
    push Not at hcon
    have hsub : Icc ξ y ⊆ Ioo 0 p.U := fun s hs => ⟨lt_of_lt_of_le hξ.1 hs.1,
      lt_of_le_of_lt hs.2 hy.2⟩
    set K := {s ∈ Icc ξ y | ψ s ≤ 0} with hK
    have hKc : IsCompact K := by
      have : IsClosed K := by
        have := (hψc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc
          (isClosed_Iic (a := (0:ℝ)))
        convert this using 1
        ext s; simp [hK]
      exact (isCompact_Icc).of_isClosed_subset this (fun s hs => hs.1)
    have hKne : K.Nonempty := ⟨ξ, ⟨le_rfl, hξy⟩, hψξ⟩
    obtain ⟨z, hzK, hzmax⟩ := hKc.exists_isGreatest hKne
    have hzy : z < y := by
      rcases lt_or_eq_of_le hzK.1.2 with h | h
      · exact h
      · exfalso; rw [h] at hzK; linarith [hzK.2]
    have hpos : ∀ s, z < s → s ≤ y → 0 < ψ s := by
      intro s hzs hsy
      by_contra hc; push Not at hc
      have : s ∈ K := ⟨⟨le_trans hzK.1.1 hzs.le, hsy⟩, hc⟩
      have := hzmax this
      linarith
    -- an interval right of z avoiding B
    have hev : ∀ᶠ t in 𝓝[>] z, t ∉ (B : Set ℝ) := by
      have hcl : IsClosed ((B : Set ℝ) \ {z}) := (B.finite_toSet.sdiff).isClosed
      have : ((B : Set ℝ) \ {z})ᶜ ∈ 𝓝 z := hcl.isOpen_compl.mem_nhds (by simp)
      have h2 : ((B : Set ℝ) \ {z})ᶜ ∈ 𝓝[>] z := mem_nhdsWithin_of_mem_nhds this
      filter_upwards [h2, self_mem_nhdsWithin] with t ht htz
      intro htB
      exact ht ⟨htB, ne_of_gt htz⟩
    obtain ⟨u, hzu, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    set t := min u y with ht
    have hzt : z < t := lt_min hzu hzy
    have hty : t ≤ y := min_le_right _ _
    have hIcc : Icc z t ⊆ Ioo 0 p.U := fun s hs =>
      hsub ⟨le_trans hzK.1.1 hs.1, le_trans hs.2 hty⟩
    have hanti : AntitoneOn ψ (Icc z t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc z t) (hψc.mono hIcc)
      · rw [interior_Icc]
        intro s hs
        have hsB : s ∉ B := by
          have := hu ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
          simpa using this
        exact (hloc s (hIcc (Ioo_subset_Icc_self hs)) hsB).1.differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro s hs
        have hsB : s ∉ B := by
          have := hu ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
          simpa using this
        have hl := hloc s (hIcc (Ioo_subset_Icc_self hs)) hsB
        rw [hl.1.deriv]
        exact (hl.2 (hpos s hs.1 (le_trans hs.2.le hty))).le
    set m := (z + t) / 2
    have hzm : z < m := by simp only [m]; linarith
    have hmt : m < t := by simp only [m]; linarith
    have h1 := hanti ⟨le_rfl, hzt.le⟩ ⟨hzm.le, hmt.le⟩ hzm.le
    have h2 := hpos m hzm (le_trans hmt.le hty)
    linarith [hzK.2]
  -- conclude
  intro x hx
  suffices hDx : 0 ≤ D x by simp only [hD] at hDx; linarith
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h; simp [hD, h0, hW0]
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · subst h'; simp [hD, hUM, hWU]
  by_contra hneg
  push Not at hneg
  have hxo : x ∈ Ioo 0 p.U := ⟨h, h'⟩
  have hDdiff : ∀ s ∈ Ioo 0 p.U, HasDerivAt D (ψ s) s := fun s hs =>
    (hWd s hs).hasDerivAt.sub (hVd s hs).hasDerivAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope D ψ h
    (hDc.mono (Icc_subset_Icc le_rfl hx.2))
    (fun s hs => hDdiff s ⟨hs.1, lt_trans hs.2 h'⟩)
  have hD0 : D 0 = 0 := by simp [hD, h0, hW0]
  rw [hD0, sub_zero] at hξeq
  have hψξ : ψ ξ < 0 := by
    rw [hξeq, sub_zero]; exact div_neg_of_neg_of_pos hneg h
  have hξo : ξ ∈ Ioo 0 p.U := ⟨hξ.1, lt_trans hξ.2 h'⟩
  have hantiD : AntitoneOn D (Icc x p.U) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc x p.U)
      (hDc.mono (Icc_subset_Icc hx.1 le_rfl))
    · rw [interior_Icc]
      intro s hs
      exact (hDdiff s ⟨lt_trans h hs.1, hs.2⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      have hs' : s ∈ Ioo 0 p.U := ⟨lt_trans h hs.1, hs.2⟩
      rw [(hDdiff s hs').deriv]
      exact hprop ξ hξo hψξ.le s hs' (le_trans hξ.2.le hs.1.le)
  have := hantiD ⟨le_rfl, h'.le⟩ ⟨h'.le, le_rfl⟩ h'.le
  have hDU : D p.U = 0 := by simp [hD, hUM, hWU]
  linarith

end DriftVarCtrl.FixedLB

open DriftVarCtrl.FixedLB in
theorem solution (p : Params) (V : ℝ → ℝ) (E : Finset ℝ)
    (hV1 : ContDiffOn ℝ 1 V (Set.Icc 0 p.U))
    (hV2 : ∀ x ∈ Set.Ioo 0 p.U, x ∉ E → ContDiffAt ℝ 2 V x)
    (h0 : V 0 = 0) (hUM : V p.U = p.M)
    (hHJB : ∀ x ∈ Set.Ioo 0 p.U, x ∉ E → ∀ c : Ctrl,
      0 ≤ p.cost c + p.mu c * deriv V x + p.sig c ^ 2 / 2 * deriv (deriv V) x)
    (π : IntervalPolicy p) (W : ℝ → ℝ) (hW : IsValue p π W) :
    ∀ x ∈ Set.Icc 0 p.U, V x ≤ W x :=
  lemma_12_analytic_proof p V E hV1 hV2 h0 hUM hHJB π W hW
