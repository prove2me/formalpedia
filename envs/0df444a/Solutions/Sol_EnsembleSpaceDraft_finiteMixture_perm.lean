-- Prove2me | solution 1 for EnsembleSpaceDraft.finiteMixture_perm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:46:36.891917+00:00
-- url     : https://prove2.me/submissions/422c53c3-7d92-4429-8ad2-c8b3384689b6

import Definitions.Def_EnsembleSpaceDraft_finiteMixture
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

universe u
namespace EnsembleSpaceDraft
namespace ENSF

variable {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)

noncomputable def nrm (s : ℝ) (t : List (ℝ × E)) : List (ℝ × E) := t.map fun pe => (pe.1 / s, pe.2)

lemma sum_nrm (s : ℝ) (t : List (ℝ × E)) :
    ((nrm s t).map Prod.fst).sum = (t.map Prod.fst).sum / s := by
  induction t with
  | nil => simp [nrm]
  | cons x t ih => simp only [nrm, List.map_map] at ih ⊢; simp [List.sum_cons, ih, add_div]

lemma nrm_nrm (s₁ s₂ : ℝ) (t : List (ℝ × E)) : nrm s₂ (nrm s₁ t) = nrm (s₁ * s₂) t := by
  simp [nrm, List.map_map, Function.comp_def, div_div]

lemma pos_nrm {s : ℝ} (hs : 0 < s) {t : List (ℝ × E)} (ht : ∀ x ∈ t, 0 < x.1) :
    ∀ x ∈ nrm s t, 0 < x.1 := by
  intro x hx
  simp only [nrm, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact div_pos (ht y hy) hs

lemma sum_pos_of_pos {t : List (ℝ × E)} (ht : ∀ x ∈ t, 0 < x.1) (hne : t ≠ []) :
    0 < (t.map Prod.fst).sum := by
  obtain ⟨x, t', rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.map_cons, List.sum_cons]
  have h1 := ht x (by simp)
  have h2 : 0 ≤ (t'.map Prod.fst).sum := List.sum_nonneg (by
    intro y hy; simp only [List.mem_map] at hy; obtain ⟨z, hz, rfl⟩ := hy
    exact (ht z (by simp [hz])).le)
  linarith

lemma nest_single (p : ℝ) (e : E) : nestMixture? X [(p, e)] = some e := by
  rw [nestMixture?]; simp

lemma nest_cons (p : ℝ) (e : E) (t : List (ℝ × E)) (hne : t ≠ [])
    (hs : (t.map Prod.fst).sum ≠ 0) :
    nestMixture? X ((p, e) :: t) =
      (nestMixture? X (nrm (t.map Prod.fst).sum t)).map
        (fun tail => X.mix (Set.projIcc (0 : ℝ) 1 zero_le_one p) e tail) := by
  rw [nestMixture?]; simp [hne, hs, nrm]

lemma projIcc_coe {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ((Set.projIcc (0 : ℝ) 1 zero_le_one p : unitInterval) : ℝ) = p := by
  rw [Set.projIcc_of_mem _ ⟨h0, h1⟩]

/-- Three-point re-association, symmetric form. -/
lemma three (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p + q < 1) (P Q : unitInterval)
    (hP : (P : ℝ) = p) (hQ : (Q : ℝ) = q / (1 - p)) (a b v : E) :
    X.mix P a (X.mix Q b v) =
      X.mix (Set.projIcc (0 : ℝ) 1 zero_le_one (p + q))
        (X.mix (Set.projIcc (0 : ℝ) 1 zero_le_one (p / (p + q))) a b) v := by
  have h := X.mix_assoc p (1 - p - q) a b v hp.le (by linarith) (by linarith) (by linarith) (by linarith)
  have e1 : X.mix P a (X.mix Q b v) = X.mix ⟨p, mem_unitInterval_of_bounds hp.le (by linarith)⟩ a
      (X.mix ⟨(1 - p - (1 - p - q)) / (1 - p), assoc_left_coeff_mem hp.le (by linarith)
        (by linarith) (by linarith) (by linarith)⟩ b v) := by
    rw [ENSL.mix_congr X (q := ⟨p, mem_unitInterval_of_bounds hp.le (by linarith)⟩) hP]
    congr 1
    apply ENSL.mix_congr; simp only; rw [hQ]; ring_nf
  rw [e1, h]
  congr 1
  · apply Subtype.ext; rw [projIcc_coe (by linarith) (by linarith)]; simp only; ring
  · apply ENSL.mix_congr
    rw [projIcc_coe (by positivity) ((div_le_one (by linarith)).mpr (by linarith))]; simp only; ring_nf

lemma swap_top (p q : ℝ) (a b : E) (r : List (ℝ × E)) (hp : 0 < p) (hq : 0 < q)
    (hr : ∀ x ∈ r, 0 < x.1) (hsum : p + q + (r.map Prod.fst).sum = 1) :
    nestMixture? X ((p, a) :: (q, b) :: r) = nestMixture? X ((q, b) :: (p, a) :: r) := by
  rcases eq_or_ne r [] with rfl | hne
  · simp only [List.map_nil, List.sum_nil, add_zero] at hsum
    rw [nest_cons X p a _ (by simp) (by simp; linarith), nest_cons X q b _ (by simp) (by simp; linarith)]
    simp only [nrm, List.map_cons, List.map_nil, nest_single, Option.map_some]
    congr 1
    rw [X.mix_comm]
    apply ENSL.mix_congr
    rw [unitInterval.coe_symm_eq, projIcc_coe hp.le (by linarith), projIcc_coe hq.le (by linarith)]
    linarith
  have hsr := sum_pos_of_pos hr hne
  have hn1 : ∀ c : ℝ, c ≠ 0 → nrm c r ≠ [] := by intro c _; simp [nrm, hne]
  have L : ∀ (p q : ℝ) (a b : E), 0 < p → 0 < q → p + q + (r.map Prod.fst).sum = 1 →
      nestMixture? X ((p, a) :: (q, b) :: r) = (nestMixture? X (nrm (r.map Prod.fst).sum r)).map
        (fun v => X.mix (Set.projIcc (0 : ℝ) 1 zero_le_one (p + q))
          (X.mix (Set.projIcc (0 : ℝ) 1 zero_le_one (p / (p + q))) a b) v) := by
    intro p q a b hp hq hsum
    have hs1 : (((q, b) :: r).map Prod.fst).sum = 1 - p := by simp; linarith
    rw [nest_cons X p a _ (by simp) (by rw [hs1]; linarith), hs1]
    have hs2 : ((nrm (1 - p) r).map Prod.fst).sum = (r.map Prod.fst).sum / (1 - p) := sum_nrm _ _
    simp only [nrm, List.map_cons]
    rw [nest_cons X _ b _ (by simpa [nrm] using hne)
      (by rw [show (List.map (fun pe : ℝ × E => (pe.1 / (1 - p), pe.2)) r) = nrm (1 - p) r from rfl, hs2]
          exact (div_pos hsr (by linarith)).ne')]
    rw [show (List.map (fun pe : ℝ × E => (pe.1 / (1 - p), pe.2)) r) = nrm (1 - p) r from rfl, hs2,
      nrm_nrm, show (1 - p) * ((r.map Prod.fst).sum / (1 - p)) = (r.map Prod.fst).sum by
        have : (1 : ℝ) - p ≠ 0 := by linarith
        field_simp]
    rw [Option.map_map]
    congr 1
    funext v
    simp only [Function.comp_apply]
    exact three X p q hp hq (by linarith) _ _ (projIcc_coe hp.le (by linarith))
      (projIcc_coe (div_nonneg hq.le (by linarith)) ((div_le_one (by linarith)).mpr (by linarith))) a b v
  rw [L p q a b hp hq hsum, L q p b a hq hp (by linarith)]
  congr 1
  funext v
  rw [add_comm q p]
  congr 1
  rw [X.mix_comm]; apply ENSL.mix_congr
  rw [unitInterval.coe_symm_eq, projIcc_coe (by positivity) ((div_le_one (by linarith)).mpr (by linarith)),
    projIcc_coe (by positivity) ((div_le_one (by linarith)).mpr (by linarith))]
  field_simp; ring

end ENSF
end EnsembleSpaceDraft

namespace EnsembleSpaceDraft
namespace ENSF

variable {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)

lemma nest_isSome : ∀ (n : ℕ) (l : List (ℝ × E)), l.length = n → l ≠ [] →
    (∀ x ∈ l, 0 < x.1) → ∃ m, nestMixture? X l = some m := by
  intro n
  induction n with
  | zero => intro l hl hne; exact absurd (List.length_eq_zero_iff.mp hl) hne
  | succ n ih =>
    intro l hl hne hpos
    obtain ⟨⟨p, e⟩, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    by_cases ht : t = []
    · subst ht; exact ⟨e, nest_single X p e⟩
    have hs := sum_pos_of_pos (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) ht
    rw [nest_cons X p e t ht hs.ne']
    obtain ⟨m, hm⟩ := ih (nrm (t.map Prod.fst).sum t) (by simp [nrm]; simpa using hl)
      (by simpa [nrm] using ht) (pos_nrm hs (fun x hx => hpos x (List.mem_cons_of_mem _ hx)))
    exact ⟨_, by rw [hm]; rfl⟩

lemma nest_perm : ∀ (n : ℕ) (l₁ l₂ : List (ℝ × E)), l₁.length = n → l₁.Perm l₂ →
    (∀ x ∈ l₁, 0 < x.1) → (l₁.map Prod.fst).sum = 1 → nestMixture? X l₁ = nestMixture? X l₂ := by
  intro n
  induction n with
  | zero =>
    intro l₁ l₂ hl hp _ _
    have h1 := List.length_eq_zero_iff.mp hl
    subst h1
    rw [List.nil_perm.mp hp]
  | succ n ih =>
    classical
    have head_eq : ∀ (x : ℝ × E) (t₁ t₂ : List (ℝ × E)), (x :: t₁).length = n + 1 →
        (x :: t₁).Perm (x :: t₂) → (∀ z ∈ x :: t₁, 0 < z.1) →
        nestMixture? X (x :: t₁) = nestMixture? X (x :: t₂) := by
      intro x t₁ t₂ hl h hpos
      obtain ⟨p, e⟩ := x
      have ht : t₁.Perm t₂ := (List.perm_cons _).mp h
      by_cases h0 : t₁ = []
      · subst h0; rw [List.nil_perm.mp ht]
      have h0' : t₂ ≠ [] := fun h' => h0 (List.Perm.eq_nil (h' ▸ ht))
      have hpos' : ∀ z ∈ t₁, 0 < z.1 := fun z hz => hpos z (List.mem_cons_of_mem _ hz)
      have hs := sum_pos_of_pos hpos' h0
      have hseq : (t₁.map Prod.fst).sum = (t₂.map Prod.fst).sum := (ht.map _).sum_eq
      rw [nest_cons X p e t₁ h0 hs.ne', nest_cons X p e t₂ h0' (hseq ▸ hs.ne'), ← hseq]
      congr 1
      apply ih
      · simp [nrm]; simpa using hl
      · exact ht.map _
      · exact pos_nrm hs hpos'
      · rw [sum_nrm, div_self hs.ne']
    intro l₁ l₂ hl hp hpos hsum
    obtain ⟨x, t₁, rfl⟩ := List.exists_cons_of_ne_nil (l := l₁) (by rintro rfl; simp at hl)
    obtain ⟨y, t₂, rfl⟩ := List.exists_cons_of_ne_nil (l := l₂)
      (by rintro rfl; exact List.cons_ne_nil _ _ (List.perm_nil.mp hp))
    by_cases hxy : x = y
    · subst hxy; exact head_eq x t₁ t₂ hl hp hpos
    have hy : y ∈ t₁ := by
      have := hp.symm.subset (List.mem_cons_self)
      rcases List.mem_cons.mp this with h | h
      · exact absurd h.symm hxy
      · exact h
    set r := t₁.erase y
    have h1 : t₁.Perm (y :: r) := List.perm_cons_erase hy
    have hpos2 : ∀ z ∈ y :: t₂, 0 < z.1 := fun z hz => hpos z (hp.symm.subset hz)
    have hsum2 : ((y :: t₂).map Prod.fst).sum = 1 := by rw [← (hp.map _).sum_eq, hsum]
    have h2 : (y :: t₂).Perm (y :: x :: r) :=
      hp.symm.trans ((h1.cons x).trans (List.Perm.swap y x r))
    have step1 := head_eq x t₁ (y :: r) hl (h1.cons x) hpos
    have step3 := head_eq y t₂ (x :: r) (by rw [← hp.length_eq]; exact hl) h2 hpos2
    have hposr : ∀ z ∈ r, 0 < z.1 := fun z hz =>
      hpos z (List.mem_cons_of_mem _ (h1.symm.subset (List.mem_cons_of_mem _ hz)))
    have hpx : 0 < x.1 := hpos x List.mem_cons_self
    have hpy : 0 < y.1 := hpos y (List.mem_cons_of_mem _ hy)
    have hsum3 : x.1 + y.1 + (r.map Prod.fst).sum = 1 := by
      have := ((h1.cons x).map Prod.fst).sum_eq
      simp only [List.map_cons, List.sum_cons] at this hsum
      linarith
    obtain ⟨p, a⟩ := x
    obtain ⟨q, b⟩ := y
    have hsw := swap_top X p q a b r hpx hpy hposr hsum3
    rw [step1, hsw, step3]

lemma sum_filter_ne (L : List (ℝ × E)) :
    ((L.filter fun pe => pe.1 ≠ 0).map Prod.fst).sum = (L.map Prod.fst).sum := by
  induction L with
  | nil => simp
  | cons x t ih =>
    by_cases h : x.1 = 0
    · simp at ih; simp [List.filter_cons, h, ih]
    · simp at ih; simp [List.filter_cons, h, ih]

end ENSF
end EnsembleSpaceDraft

open EnsembleSpaceDraft
open scoped BigOperators

theorem solution {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E) {n : ℕ}
    (p : Fin n → ℝ) (e : Fin n → E) (τ : Equiv.Perm (Fin n))
    (hnn : ∀ i, 0 ≤ p i) (hle : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = 1) :
    ∃ m : E,
      finiteMixture X p e = some m ∧
        finiteMixture X (fun i => p (τ i)) (fun i => e (τ i)) = some m := by
  set L := List.ofFn fun i => (p i, e i) with hL
  have hperm : (List.ofFn fun i => (p (τ i), e (τ i))).Perm L :=
    Equiv.Perm.ofFn_comp_perm τ (fun i => (p i, e i))
  set F := L.filter fun pe => pe.1 ≠ 0 with hF
  have hposF : ∀ x ∈ F, 0 < x.1 := by
    intro x hx
    rw [hF, List.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [hL, List.mem_ofFn] at hx1
    obtain ⟨i, rfl⟩ := hx1
    exact lt_of_le_of_ne (hnn i) (Ne.symm (by simpa using hx2))
  have hsumF : (F.map Prod.fst).sum = 1 := by
    rw [hF, ENSF.sum_filter_ne, hL, List.map_ofFn, List.sum_ofFn]
    exact hsum
  have hneF : F ≠ [] := by rintro h; rw [h] at hsumF; simp at hsumF
  obtain ⟨m, hm⟩ := ENSF.nest_isSome X _ F rfl hneF hposF
  refine ⟨m, hm, ?_⟩
  have hpF : ((List.ofFn fun i => (p (τ i), e (τ i))).filter fun pe => pe.1 ≠ 0).Perm F :=
    hperm.filter _
  show nestMixture? X _ = some m
  rw [← hm]
  exact (ENSF.nest_perm X _ F _ rfl hpF.symm hposF hsumF).symm
