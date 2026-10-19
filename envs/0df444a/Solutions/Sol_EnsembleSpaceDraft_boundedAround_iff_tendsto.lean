-- Prove2me | solution 1 for EnsembleSpaceDraft.boundedAround_iff_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:38:17.446893+00:00
-- url     : https://prove2.me/submissions/f4e9f5ab-fd01-496c-974a-f1fcc0beae94

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

open scoped unitInterval

namespace EnsembleSpaceDraft

universe u

namespace ENSL

variable {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)

lemma mix_zero (a b : E) : X.mix 0 a b = b := by
  rw [X.mix_comm, unitInterval.symm_zero, X.mix_one]

lemma mix_of_eq_one {p : unitInterval} (hp : (p : ℝ) = 1) (a b : E) : X.mix p a b = a := by
  have : p = 1 := Subtype.ext hp
  subst this; exact X.mix_one a b

lemma mix_of_eq_zero {p : unitInterval} (hp : (p : ℝ) = 0) (a b : E) : X.mix p a b = b := by
  have : p = 0 := Subtype.ext hp
  subst this; exact mix_zero X a b

lemma mix_congr {p q : unitInterval} (h : (p : ℝ) = q) (a b : E) : X.mix p a b = X.mix q a b := by
  rw [Subtype.ext h]

/-- Re-association: `u (v x + (1-v) y) + (1-u) z = (u v) x + (1 - u v) (w y + (1-w) z)`. -/
lemma assoc_right (u v : unitInterval) (x y z : E) :
    ∃ w : unitInterval, X.mix u (X.mix v x y) z =
      X.mix ⟨(u : ℝ) * v, unitInterval.mul_mem u.2 v.2⟩ x (X.mix w y z) := by
  have hu0 := u.2.1; have hu1 := u.2.2; have hv0 := v.2.1; have hv1 := v.2.2
  rcases eq_or_lt_of_le hu0 with hu | hu
  · refine ⟨0, ?_⟩
    rw [mix_of_eq_zero X hu.symm, mix_of_eq_zero X (by simp [← hu]), mix_zero]
  by_cases huv : (u : ℝ) * v = 1
  · have hu1' : (u : ℝ) = 1 := by nlinarith
    have hv1' : (v : ℝ) = 1 := by nlinarith
    refine ⟨0, ?_⟩
    rw [mix_of_eq_one X hu1', mix_of_eq_one X hv1', mix_of_eq_one X huv]
  have huv1 : (u : ℝ) * v < 1 := lt_of_le_of_ne (unitInterval.mul_mem u.2 v.2).2 huv
  have h := X.mix_assoc ((u : ℝ) * v) (1 - u) x y z (mul_nonneg hu0 hv0) huv1
    (by linarith) (by linarith) (by nlinarith)
  refine ⟨⟨(1 - (u : ℝ) * v - (1 - u)) / (1 - u * v), assoc_left_coeff_mem (mul_nonneg hu0 hv0)
    huv1 (by linarith) (by linarith) (by nlinarith)⟩, ?_⟩
  rw [h]
  have hu' : (1 : ℝ) - (1 - u) ≠ 0 := by linarith
  congr 1
  · apply Subtype.ext; simp
  · congr 1; apply Subtype.ext; simp only; field_simp; ring

/-- `s e + (1-s) (t e + (1-t) a) = (s + (1-s) t) e + ... a`. -/
lemma mix_mix_same (s t : unitInterval) (e a : E) :
    X.mix s e (X.mix t e a) =
      X.mix ⟨(s : ℝ) + (1 - s) * t, by
        constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩ e a := by
  have hs0 := s.2.1; have hs1 := s.2.2; have ht0 := t.2.1; have ht1 := t.2.2
  rcases eq_or_lt_of_le hs1 with hs | hs
  · rw [mix_of_eq_one X hs, mix_of_eq_one X (by simp [hs])]
  by_cases h00 : (s : ℝ) = 0 ∧ (t : ℝ) = 0
  · rw [mix_of_eq_zero X h00.1, mix_of_eq_zero X h00.2, mix_of_eq_zero X (by simp [h00.1, h00.2])]
  have hp3 : (1 - (s : ℝ)) * (1 - t) < 1 := by
    by_contra hc
    push Not at hc
    have : (1 - (s : ℝ)) * (1 - t) ≤ 1 - s := by nlinarith
    have hs0' : (s : ℝ) = 0 := by linarith
    have : (t : ℝ) = 0 := by
      rw [hs0'] at hc; nlinarith
    exact h00 ⟨hs0', this⟩
  have h := X.mix_assoc (s : ℝ) ((1 - s) * (1 - t)) e e a hs0 hs
    (by nlinarith) hp3 (by nlinarith)
  rw [X.mix_self] at h
  convert h using 2
  · congr 1; apply Subtype.ext; simp; field_simp; ring
  · apply Subtype.ext; simp; ring

/-- Components compose. -/
lemma component_trans {c m n : E} (h1 : X.IsComponent c m) (h2 : X.IsComponent m n) :
    X.IsComponent c n := by
  obtain ⟨s, d1, hs, rfl⟩ := h1
  obtain ⟨r, d, hr, rfl⟩ := h2
  obtain ⟨w, hw⟩ := assoc_right X r s c d1 d
  exact ⟨_, _, by simp only; positivity, hw⟩

/-- For `0 < p ≤ q`, `p x + (1-p) y = (p/q) (q x + (1-q) y) + (1 - p/q) y`. -/
lemma mix_as_component (p q : unitInterval) (hp : 0 < (p : ℝ)) (hpq : (p : ℝ) ≤ q) (x y : E) :
    X.IsComponent (X.mix q x y) (X.mix p x y) := by
  have hq : 0 < (q : ℝ) := lt_of_lt_of_le hp hpq
  have hr : (p : ℝ) / q ∈ unitInterval :=
    ⟨div_nonneg p.2.1 hq.le, (div_le_one hq).mpr hpq⟩
  obtain ⟨w, hw⟩ := assoc_right X ⟨_, hr⟩ q x y y
  refine ⟨⟨_, hr⟩, y, div_pos hp hq, ?_⟩
  rw [hw, X.mix_self]
  apply mix_congr; simp; field_simp

end ENSL

end EnsembleSpaceDraft

open EnsembleSpaceDraft
universe u
open scoped unitInterval
open Filter Topology

theorem solution {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)
    (A : Set E) (e : E) :
    X.BoundedAround A e ↔
      ∀ (p : ℕ → unitInterval) (a : ℕ → E),
        (∀ n, a n ∈ A) → Tendsto (fun n => (p n : ℝ)) atTop (nhds 1) →
          Tendsto (fun n => X.mix (p n) e (a n)) atTop (nhds e) := by
  constructor
  · intro hB p a ha hp
    rw [tendsto_nhds]
    intro U hU heU
    have hcont : Continuous fun x : unitInterval × E => X.mix x.1 e x.2 :=
      X.continuous_mix.comp
        (show Continuous (fun x : unitInterval × E => (x.1, e, x.2)) by fun_prop)
    set N := (fun x : unitInterval × E => X.mix x.1 e x.2) ⁻¹' U with hNdef
    have hN : IsOpen N := hU.preimage hcont
    have hsub : (Set.univ : Set unitInterval) ×ˢ ({e} : Set E) ⊆ N := by
      rintro ⟨s, x⟩ ⟨_, hx⟩
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp [N, X.mix_self, heU]
    obtain ⟨u, V, _, hV, hu', heV, huv⟩ :=
      generalized_tube_lemma isCompact_univ isCompact_singleton hN hsub
    obtain ⟨p0, hp0, himg⟩ := hB V hV (heV rfl)
    have hev : ∀ᶠ n in atTop, (p0 : ℝ) < p n := hp.eventually (lt_mem_nhds hp0)
    filter_upwards [hev] with n hn
    have hs : ((p n : ℝ) - p0) / (1 - p0) ∈ unitInterval :=
      ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).mpr (by linarith [(p n).2.2])⟩
    have h1 := ENSL.mix_mix_same X ⟨_, hs⟩ p0 e (a n)
    have h2 : X.mix (p n) e (a n) = X.mix ⟨_, hs⟩ e (X.mix p0 e (a n)) := by
      rw [h1]; apply ENSL.mix_congr; simp only
      have : (1 : ℝ) - p0 ≠ 0 := by linarith
      field_simp; ring
    show X.mix (p n) e (a n) ∈ U
    rw [h2]
    have hm : X.mix p0 e (a n) ∈ V := himg ⟨a n, ha n, rfl⟩
    exact huv (Set.mk_mem_prod (hu' (Set.mem_univ _)) hm)
  · intro H
    by_contra hB
    simp only [EnsembleSpace.BoundedAround, not_forall, not_exists, not_and] at hB
    obtain ⟨U, hU, heU, hne⟩ := hB
    have hq : ∀ n : ℕ, (1 : ℝ) - 1 / ((n : ℝ) + 1) ∈ unitInterval := by
      intro n
      have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      exact ⟨by linarith, by linarith [show (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) by positivity]⟩
    have hex : ∀ n : ℕ, ∃ a ∈ A, X.mix ⟨_, hq n⟩ e a ∉ U := by
      intro n
      have hlt : ((⟨_, hq n⟩ : unitInterval) : ℝ) < 1 := by
        simp only; linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
      have := hne ⟨_, hq n⟩ hlt
      rw [Set.image_subset_iff] at this
      simpa [Set.subset_def] using this
    choose a ha haU using hex
    have ht : Tendsto (fun n : ℕ => ((⟨_, hq n⟩ : unitInterval) : ℝ)) atTop (nhds 1) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (1 : ℝ)
      simpa using this
    have := H (fun n => ⟨_, hq n⟩) a ha ht
    obtain ⟨n, hn⟩ := (this.eventually (hU.mem_nhds heU)).exists
    exact haU n hn
