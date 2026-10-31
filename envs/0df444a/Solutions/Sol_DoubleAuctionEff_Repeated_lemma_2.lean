-- Prove2me | solution 1 for DoubleAuctionEff.Repeated.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:00:51.021601+00:00
-- url     : https://prove2.me/submissions/bb535249-8683-41dc-b6f1-b7afa07bbb47

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

open DoubleAuctionEff.Repeated

namespace DAELemma2Aux

theorem u_ne_top {J : Type*} {u : (J → ℝ) → EReal} {g : J → ℝ} (h1 : Assumption1 u g)
    (x : J → ℝ) : u x ≠ ⊤ := by
  intro h
  have hx : x ∈ dom u := by simp [dom, h]
  have := h1.2.2 x hx 1 one_pos
  rw [h] at this
  exact not_top_lt this

theorem mono_g {J : Type*} {u : (J → ℝ) → EReal} {g : J → ℝ} (h1 : Assumption1 u g)
    (z : J → ℝ) {s : ℝ} (hs : 0 ≤ s) : u z ≤ u (z + s • g) := by
  rcases hs.lt_or_eq with hs | hs
  · by_cases hz : z ∈ dom u
    · exact (h1.2.2 z hz s hs).le
    · simp only [dom, Set.mem_setOf_eq, not_lt, le_bot_iff] at hz
      simp [hz]
  · subst hs; simp

theorem le_indiff {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {r : ℝ}
    (h : u x0 ≤ u (x0 + y - r • g)) : (r : EReal) ≤ indiffPrice u g x0 y := by
  unfold indiffPrice
  exact le_iSup₂ (f := fun (r : ℝ) (_ : u x0 ≤ u (x0 + y - r • g)) => (r : EReal)) r h

theorem admissible_of_lt {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {r : ℝ}
    (h1 : Assumption1 u g) (h : (r : EReal) < indiffPrice u g x0 y) :
    u x0 ≤ u (x0 + y - r • g) := by
  unfold indiffPrice at h
  obtain ⟨r', hr'⟩ := lt_iSup_iff.1 h
  obtain ⟨hadm, hlt⟩ := lt_iSup_iff.1 hr'
  rw [EReal.coe_lt_coe_iff] at hlt
  have := mono_g h1 (x0 + y - r' • g) (s := r' - r) (by linarith)
  refine hadm.trans (this.trans (le_of_eq ?_))
  congr 1; rw [sub_smul]; abel

theorem indiff_attained {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {c : ℝ}
    (husc : UpperSemicontinuous u) (hc : indiffPrice u g x0 y = (c : EReal)) :
    u x0 ≤ u (x0 + y - c • g) := by
  by_contra hlt
  push_neg at hlt
  have hcont : Continuous (fun r : ℝ => x0 + y - r • g) := by fun_prop
  have hev : ∀ᶠ r in nhds c, u (x0 + y - r • g) < u x0 :=
    hcont.continuousAt.eventually (husc _ _ hlt)
  rcases Metric.eventually_nhds_iff.1 hev with ⟨ε, hε, hball⟩
  have hle : indiffPrice u g x0 y ≤ ((c - ε : ℝ) : EReal) := by
    unfold indiffPrice
    refine iSup₂_le fun r hr => ?_
    have hrc : (r : EReal) ≤ c := hc ▸ le_indiff hr
    rw [EReal.coe_le_coe_iff] at hrc ⊢
    by_contra hcon
    push_neg at hcon
    have hd : dist r c < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    exact absurd hr (not_le.2 (hball hd))
  rw [hc, EReal.coe_le_coe_iff] at hle
  linarith

/-- Characterization of the real lower level sets of the indifference price. -/
theorem le_indiff_iff {J : Type*} {u : (J → ℝ) → EReal} {g x0 : J → ℝ} (h1 : Assumption1 u g)
    (y : J → ℝ) (α : ℝ) :
    (α : EReal) ≤ indiffPrice u g x0 y ↔ u x0 ≤ u (x0 + y - α • g) := by
  refine ⟨fun h => ?_, le_indiff⟩
  rcases h.lt_or_eq with h | h
  · exact admissible_of_lt h1 h
  · exact indiff_attained h1.1 h.symm

theorem eq_of_real_le_iff {a b : EReal} (h : ∀ α : ℝ, (α : EReal) ≤ a ↔ (α : EReal) ≤ b) :
    a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨α, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    exact absurd ((h α).2 h2.le) (not_le.2 h1)
  · obtain ⟨α, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    exact absurd ((h α).1 h2.le) (not_le.2 h1)

end DAELemma2Aux

open DAELemma2Aux in
theorem solution {J : Type*} [Fintype J] (u : (J → ℝ) → EReal) (g x0 : J → ℝ)
    (h1 : Assumption1 u g) (hx0 : x0 ∈ dom u) :
    IsConcaveE (indiffPrice u g x0) ∧ UpperSemicontinuous (indiffPrice u g x0) ∧
      indiffPrice u g x0 0 = 0 ∧
      ∀ y ∈ dom (indiffPrice u g x0), ∀ r : ℝ,
        indiffPrice u g x0 (y + r • g) = indiffPrice u g x0 y + (r : EReal) := by
  set ℓ : ℝ := (u x0).toReal
  have hℓ : u x0 = (ℓ : EReal) := (EReal.coe_toReal (u_ne_top h1 x0) (ne_of_gt hx0)).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- concavity
    rintro ⟨y1, a⟩ ha ⟨y2, b⟩ hb θ μ hθ hμ hθμ
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [le_indiff_iff h1] at ha hb
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rw [le_indiff_iff h1]
    have hA : ((x0 + y1 - a • g, ℓ) : (J → ℝ) × ℝ) ∈
        {q : (J → ℝ) × ℝ | ((q.2 : ℝ) : EReal) ≤ u q.1} := by
      show (ℓ : EReal) ≤ _; rw [← hℓ]; exact ha
    have hB : ((x0 + y2 - b • g, ℓ) : (J → ℝ) × ℝ) ∈
        {q : (J → ℝ) × ℝ | ((q.2 : ℝ) : EReal) ≤ u q.1} := by
      show (ℓ : EReal) ≤ _; rw [← hℓ]; exact hb
    have hC := h1.2.1 hA hB hθ hμ hθμ
    simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hC
    have hpt : θ • (x0 + y1 - a • g) + μ • (x0 + y2 - b • g) =
        x0 + (θ • y1 + μ • y2) - (θ * a + μ * b) • g := by
      have hμ' : μ = 1 - θ := by linarith
      subst hμ'
      simp only [smul_add, smul_sub, smul_smul, add_smul, sub_smul, one_smul]
      abel
    rw [hpt, ← add_mul, hθμ, one_mul] at hC
    rw [hℓ]; exact hC
  · -- upper semicontinuity
    rw [upperSemicontinuous_iff_isClosed_preimage]
    have hreal : ∀ α : ℝ, IsClosed (indiffPrice u g x0 ⁻¹' Set.Ici (α : EReal)) := by
      intro α
      have : indiffPrice u g x0 ⁻¹' Set.Ici (α : EReal) =
          (fun y => x0 + y - α • g) ⁻¹' (u ⁻¹' Set.Ici (u x0)) := by
        ext y; simp only [Set.mem_preimage, Set.mem_Ici]; exact le_indiff_iff h1 y α
      rw [this]
      exact (h1.1.isClosed_preimage (u x0)).preimage (by fun_prop)
    intro z
    induction z using EReal.rec with
    | bot => simp
    | top =>
      have : indiffPrice u g x0 ⁻¹' Set.Ici (⊤ : EReal) =
          ⋂ n : ℕ, indiffPrice u g x0 ⁻¹' Set.Ici ((n : ℝ) : EReal) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_Ici, top_le_iff, Set.mem_iInter]
        refine ⟨fun h n => by rw [h]; exact le_top, fun h => ?_⟩
        refine EReal.eq_top_iff_forall_lt _ |>.2 fun α => ?_
        obtain ⟨n, hn⟩ := exists_nat_gt α
        exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hn) (h n)
      rw [this]
      exact isClosed_iInter fun n => hreal n
    | coe α => exact hreal α
  · -- D(0) = 0
    apply le_antisymm
    · unfold indiffPrice
      refine iSup₂_le fun r hr => ?_
      rw [← EReal.coe_zero, EReal.coe_le_coe_iff]
      by_contra hpos
      push_neg at hpos
      have hz : x0 + 0 - r • g ∈ dom u := lt_of_lt_of_le hx0 hr
      have := h1.2.2 _ hz r hpos
      rw [add_zero, sub_add_cancel] at this
      exact absurd hr (not_le.2 (by simpa using this))
    · have := le_indiff (u := u) (g := g) (x0 := x0) (y := 0) (r := 0) (by simp)
      simpa using this
  · -- translation along g
    intro y hy r
    apply eq_of_real_le_iff
    intro α
    rw [le_indiff_iff h1]
    have hpt : x0 + (y + r • g) - α • g = x0 + y - (α - r) • g := by
      rw [sub_smul]; abel
    rw [hpt, ← le_indiff_iff h1]
    simp only [dom, Set.mem_setOf_eq] at hy
    induction h : indiffPrice u g x0 y using EReal.rec with
    | bot => rw [h] at hy; exact absurd hy (lt_irrefl _)
    | top => simp
    | coe d =>
      rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      constructor <;> intro h' <;> linarith
