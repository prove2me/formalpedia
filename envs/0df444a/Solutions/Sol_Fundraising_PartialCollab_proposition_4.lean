-- Prove2me | solution 1 for Fundraising.PartialCollab.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T16:14:50.630915+00:00
-- url     : https://prove2.me/submissions/43f9f718-a973-4c1a-b0f8-0392ea004865

import Mathlib
import Definitions.Def_Fundraising_PartialCollab_Setting
import Theorems.Thm_Fundraising_PartialCollab_eq_S11
import Theorems.Thm_Fundraising_PartialCollab_log_concavity
import Theorems.Thm_Fundraising_PartialCollab_effort_system

namespace Fundraising.PartialCollab.FR3M

open Finset Fundraising.PartialCollab

theorem sum_exp_update {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ∑ j, Real.exp (Function.update s i t j) =
      Real.exp t + ∑ j ∈ univ.erase i, Real.exp (s j) := by
  rw [← Finset.add_sum_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem theta_update {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    theta (Function.update s i t) i =
      Real.exp t / (1 + Real.exp t + ∑ j ∈ univ.erase i, Real.exp (s j)) := by
  unfold theta
  rw [sum_exp_update, Function.update_self, add_assoc]

theorem R_nonneg {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    0 ≤ ∑ j ∈ univ.erase i, Real.exp (s j) :=
  Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)

theorem theta_update_pos {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    0 < theta (Function.update s i t) i := by
  rw [theta_update]
  have := R_nonneg s i
  positivity

theorem theta_pos {n : ℕ} (s : Fin n → ℝ) (i : Fin n) : 0 < theta s i := by
  have := theta_update_pos s i (s i)
  rwa [Function.update_eq_self] at this

theorem theta_update_hasDerivAt {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    DifferentiableAt ℝ (fun t => theta (Function.update s i t) i) t := by
  have hR := R_nonneg s i
  have : (fun t => theta (Function.update s i t) i) =
      fun t => Real.exp t / (1 + Real.exp t + ∑ j ∈ univ.erase i, Real.exp (s j)) :=
    funext (theta_update s i)
  rw [this]
  exact Real.differentiableAt_exp.div (by fun_prop) (by positivity)

/-- KKT ⟺ maximality for one HO. -/
theorem kkt_iff {n : ℕ} (G : Setting n) (hG : G.Standing) (s : Fin n → ℝ) (i : Fin n)
    (hsi : s i ∈ Set.Icc (G.a i) (G.b i)) :
    IsMaxOn (fun t => G.δ i t * theta (Function.update s i t) i)
        (Set.Icc (G.a i) (G.b i)) (s i) ↔
    ∃ μ₁ μ₂ : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧
          deriv (G.δ i) (s i) / G.δ i (s i) +
              deriv (fun t => theta (Function.update s i t) i) (s i) / theta s i +
              μ₁ - μ₂ = 0 ∧
          μ₁ * (G.a i - s i) = 0 ∧
          μ₂ * (s i - G.b i) = 0 := by
  obtain ⟨l, r, hl, hr, hδpos, hδdiff, _⟩ := hG.δ_regular i
  have hsub : Set.Icc (G.a i) (G.b i) ⊆ Set.Ioo l r := fun t ht =>
    ⟨lt_of_lt_of_le hl ht.1, lt_of_le_of_lt ht.2 hr⟩
  set S := Set.Icc (G.a i) (G.b i) with hS
  set θu := fun t => theta (Function.update s i t) i with hθu
  set f := fun t => G.δ i t * θu t with hf
  set g := fun t => Real.log (f t) with hg
  set D := deriv (G.δ i) (s i) / G.δ i (s i) + deriv θu (s i) / theta s i with hD
  have hθs : θu (s i) = theta s i := by simp [hθu, Function.update_eq_self]
  have hδs : 0 < G.δ i (s i) := hδpos _ (hsub hsi)
  have hθpos : 0 < theta s i := theta_pos s i
  have hfpos : ∀ t ∈ S, 0 < f t := fun t ht =>
    mul_pos (hδpos t (hsub ht)) (theta_update_pos s i t)
  have hδd : HasDerivAt (G.δ i) (deriv (G.δ i) (s i)) (s i) :=
    ((hδdiff.differentiableAt (Ioo_mem_nhds (hsub hsi).1 (hsub hsi).2))).hasDerivAt
  have hθd : HasDerivAt θu (deriv θu (s i)) (s i) :=
    (theta_update_hasDerivAt s i (s i)).hasDerivAt
  have hgd : HasDerivAt g D (s i) := by
    have hm : HasDerivAt f (deriv (G.δ i) (s i) * θu (s i) + G.δ i (s i) * deriv θu (s i))
        (s i) := hδd.mul hθd
    have hfs : f (s i) ≠ 0 := by
      show G.δ i (s i) * θu (s i) ≠ 0
      rw [hθs]; exact (mul_pos hδs hθpos).ne'
    have h1 := hm.log hfs
    convert h1 using 1
    show _ = _ / (G.δ i (s i) * θu (s i))
    rw [hθs, hD]
    field_simp
  have hconc : ConcaveOn ℝ S g := log_concavity G hG i s
  -- maximality of f ⟺ maximality of g
  have hfg : IsMaxOn f S (s i) ↔ ∀ t ∈ S, (t - s i) * D ≤ 0 := by
    constructor
    · intro hmax t ht
      have hgmax : IsMaxOn g S (s i) := isMaxOn_iff.2 fun u hu =>
        Real.log_le_log (hfpos u hu) (isMaxOn_iff.1 hmax u hu)
      have hloc : IsLocalMaxOn g S (s i) := hgmax.localize
      have hy : t - s i ∈ posTangentConeAt S (s i) :=
        sub_mem_posTangentConeAt_of_segment_subset ((convex_Icc _ _).segment_subset hsi ht)
      have := hloc.hasFDerivWithinAt_nonpos hgd.hasDerivWithinAt.hasFDerivWithinAt hy
      simpa using this
    · intro hkkt
      refine isMaxOn_iff.2 fun t ht => ?_
      have hgle : g t ≤ g (s i) := by
        rcases lt_trichotomy t (s i) with h | h | h
        · have h1 := hconc.le_slope_of_hasDerivAt ht hsi h hgd
          rw [slope_def_field] at h1
          rw [le_div_iff₀ (by linarith)] at h1
          have := hkkt t ht
          nlinarith
        · rw [h]
        · have h1 := hconc.slope_le_of_hasDerivAt hsi ht h hgd
          rw [slope_def_field] at h1
          rw [div_le_iff₀ (by linarith)] at h1
          have := hkkt t ht
          nlinarith
      exact (Real.log_le_log_iff (hfpos t ht) (hfpos _ hsi)).1 hgle
  rw [hfg]
  constructor
  · intro h
    refine ⟨max (-D) 0, max D 0, le_max_right _ _, le_max_right _ _, ?_, ?_, ?_⟩
    · rcases le_total D 0 with h0 | h0
      · rw [max_eq_left (by linarith), max_eq_right h0]; ring
      · rw [max_eq_right (by linarith), max_eq_left h0]; ring
    · rcases le_total D 0 with h0 | h0
      · rcases eq_or_lt_of_le hsi.1 with he | hlt
        · rw [he]; ring
        · rcases eq_or_lt_of_le h0 with hD0 | hD0
          · rw [hD0]; simp
          · have := h (G.a i) ⟨le_refl _, hG.a_le_b i⟩
            nlinarith
      · rw [max_eq_right (by linarith)]; ring
    · rcases le_total D 0 with h0 | h0
      · rw [max_eq_right h0]; ring
      · rcases eq_or_lt_of_le hsi.2 with he | hlt
        · rw [he]; ring
        · rcases eq_or_lt_of_le h0 with hD0 | hD0
          · rw [← hD0]; simp
          · have := h (G.b i) ⟨hG.a_le_b i, le_refl _⟩
            nlinarith
  · rintro ⟨μ₁, μ₂, h1, h2, h3, h4, h5⟩ t ht
    have hDe : D = μ₂ - μ₁ := by linarith
    rw [hDe]
    nlinarith [ht.1, ht.2]


/-- Topkis-type monotone comparative statics for the MNL objective. -/
theorem topkis {δ : ℝ → ℝ} {a b R R' σ σ' : ℝ}
    (hδ : ∀ t ∈ Set.Icc a b, 0 < δ t) (hR : 0 ≤ R) (hRR : R < R')
    (hσ : σ ∈ Set.Icc a b) (hσ' : σ' ∈ Set.Icc a b)
    (h1 : ∀ t ∈ Set.Icc a b, δ t * Real.exp t / (1 + Real.exp t + R) ≤
      δ σ * Real.exp σ / (1 + Real.exp σ + R))
    (h2 : ∀ t ∈ Set.Icc a b, δ t * Real.exp t / (1 + Real.exp t + R') ≤
      δ σ' * Real.exp σ' / (1 + Real.exp σ' + R')) :
    σ ≤ σ' := by
  by_contra hlt
  push Not at hlt
  have he : Real.exp σ' < Real.exp σ := Real.exp_lt_exp.2 hlt
  set A := δ σ * Real.exp σ
  set A' := δ σ' * Real.exp σ'
  have hA : 0 < A := mul_pos (hδ σ hσ) (Real.exp_pos _)
  have hA' : 0 < A' := mul_pos (hδ σ' hσ') (Real.exp_pos _)
  have hp1 : 0 < 1 + Real.exp σ + R := by positivity
  have hp2 : 0 < 1 + Real.exp σ' + R := by positivity
  have hp3 : 0 < 1 + Real.exp σ + R' := by have := Real.exp_pos σ; linarith
  have hp4 : 0 < 1 + Real.exp σ' + R' := by have := Real.exp_pos σ'; linarith
  have k1 := h1 σ' hσ'
  have k2 := h2 σ hσ
  rw [div_le_div_iff₀ hp2 hp1] at k1
  rw [div_le_div_iff₀ hp3 hp4] at k2
  have hAA : A ≤ A' := by nlinarith
  nlinarith

theorem existence {n : ℕ} [NeZero n] (G : Setting n) (hG : G.Standing) :
    ∃ s x : Fin n → ℝ, G.IsNE s x := by
  classical
  -- objective
  let φ : Fin n → ℝ → ℝ → ℝ := fun i R t => G.δ i t * Real.exp t / (1 + Real.exp t + R)
  have hδpos : ∀ i, ∀ t ∈ Set.Icc (G.a i) (G.b i), 0 < G.δ i t := by
    intro i t ht
    obtain ⟨l, r, hl, hr, hδp, _, _⟩ := hG.δ_regular i
    exact hδp t ⟨lt_of_lt_of_le hl ht.1, lt_of_le_of_lt ht.2 hr⟩
  have hex : ∀ i, ∀ R : ℝ, 0 ≤ R → ∃ σ ∈ Set.Icc (G.a i) (G.b i),
      IsMaxOn (φ i R) (Set.Icc (G.a i) (G.b i)) σ := by
    intro i R hR
    obtain ⟨l, r, hl, hr, _, hδdiff, _⟩ := hG.δ_regular i
    have hsub : Set.Icc (G.a i) (G.b i) ⊆ Set.Ioo l r := fun t ht =>
      ⟨lt_of_lt_of_le hl ht.1, lt_of_le_of_lt ht.2 hr⟩
    have hc : ContinuousOn (φ i R) (Set.Icc (G.a i) (G.b i)) := by
      apply ContinuousOn.div
      · exact (hδdiff.continuousOn.mono hsub).mul Real.continuous_exp.continuousOn
      · fun_prop
      · intro t _; positivity
    exact isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (hG.a_le_b i)) hc
  let h : Fin n → ℝ → ℝ := fun i R =>
    if hR : 0 ≤ R then (hex i R hR).choose else G.a i
  have hmem : ∀ i R, h i R ∈ Set.Icc (G.a i) (G.b i) := by
    intro i R
    by_cases hR : 0 ≤ R
    · simp only [h, dif_pos hR]; exact (hex i R hR).choose_spec.1
    · simp only [h, dif_neg hR]; exact ⟨le_refl _, hG.a_le_b i⟩
  have hmax : ∀ i R, 0 ≤ R → IsMaxOn (φ i R) (Set.Icc (G.a i) (G.b i)) (h i R) := by
    intro i R hR
    simp only [h, dif_pos hR]; exact (hex i R hR).choose_spec.2
  have hmono : ∀ i R R', 0 ≤ R → R ≤ R' → h i R ≤ h i R' := by
    intro i R R' hR hRR
    rcases eq_or_lt_of_le hRR with he | hlt
    · rw [he]
    · exact topkis (hδpos i) hR hlt (hmem i R) (hmem i R')
        (fun t ht => isMaxOn_iff.1 (hmax i R hR) t ht)
        (fun t ht => isMaxOn_iff.1 (hmax i R' (hR.trans hRR)) t ht)
  -- lattice
  haveI : ∀ i, Fact (G.a i ≤ G.b i) := fun i => ⟨hG.a_le_b i⟩
  let T := (i : Fin n) → Set.Icc (G.a i) (G.b i)
  let F : T →o T :=
    { toFun := fun s i => ⟨h i (∑ j ∈ univ.erase i, Real.exp (s j : ℝ)),
        hmem i _⟩
      monotone' := by
        intro s s' hss i
        show h i _ ≤ h i _
        apply hmono i _ _ (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le))
        apply Finset.sum_le_sum
        intro j _
        exact Real.exp_le_exp.2 (hss j) }
  let sT : T := OrderHom.lfp F
  have hfix : F sT = sT := F.map_lfp
  let s : Fin n → ℝ := fun i => (sT i : ℝ)
  have hs_eq : ∀ i, s i = h i (∑ j ∈ univ.erase i, Real.exp (s j)) := by
    intro i
    have := congrArg (fun u : T => (u i : ℝ)) hfix
    exact this.symm
  have hsbox : ∀ i, s i ∈ Set.Icc (G.a i) (G.b i) := fun i => (sT i).2
  have hsmax : ∀ i, IsMaxOn (fun t => G.δ i t * theta (Function.update s i t) i)
      (Set.Icc (G.a i) (G.b i)) (s i) := by
    intro i
    have hm := hmax i _ (R_nonneg s i)
    rw [← hs_eq i] at hm
    refine isMaxOn_iff.2 fun t ht => ?_
    have := isMaxOn_iff.1 hm t ht
    simp only [φ] at this
    rw [theta_update, theta_update]
    rw [mul_div_assoc, mul_div_assoc] at this
    exact this
  -- efforts
  have hαpos : ∀ i, 0 < G.alpha s i := by
    intro i
    unfold Setting.alpha
    exact lt_min (div_pos (hG.B_pos i) (mul_pos (hδpos i _ (hsbox i)) (theta_pos s i))) one_pos
  have hαle : ∀ i, G.alpha s i ≤ 1 := fun i => min_le_right _ _
  obtain ⟨i0, _, hi0⟩ := Finset.exists_max_image univ (G.alpha s) univ_nonempty
  let x : Fin n → ℝ := fun j => if j = i0 then G.alpha s i0 else 0
  have hxbox : G.InBox s x := by
    intro i
    refine ⟨hsbox i, ?_⟩
    simp only [x]
    split_ifs
    · exact ⟨(hαpos i0).le, hαle i0⟩
    · exact ⟨le_refl _, zero_le_one⟩
  refine ⟨s, x, (eq_S11 G hG s x hxbox).2 fun i => ⟨hsmax i, ?_⟩⟩
  have hsum : ∑ j ∈ univ.erase i, x j = if i0 ∈ univ.erase i then G.alpha s i0 else 0 := by
    simp only [x]
    rw [Finset.sum_ite_eq']
  by_cases hii : i = i0
  · subst hii
    rw [hsum, if_neg (Finset.notMem_erase _ _)]
    simp only [x, if_pos rfl, sub_zero]
    exact (max_eq_left (hαpos _).le).symm
  · rw [hsum, if_pos (Finset.mem_erase.2 ⟨Ne.symm hii, mem_univ _⟩)]
    simp only [x, if_neg hii]
    have := hi0 i (mem_univ _)
    exact (max_eq_right (by linarith)).symm

end Fundraising.PartialCollab.FR3M

open Fundraising.PartialCollab Finset in
theorem solution {n : ℕ} [NeZero n] (G : Setting n) (hG : G.Standing) :
    (∃ s x : Fin n → ℝ, G.IsNE s x) ∧
    ∀ s x : Fin n → ℝ, G.InBox s x → Antitone (G.alpha s) →
      (G.IsNE s x ↔
        (∀ i : Fin n, ∃ μ₁ μ₂ : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧
          deriv (G.δ i) (s i) / G.δ i (s i) +
              deriv (fun t => theta (Function.update s i t) i) (s i) / theta s i +
              μ₁ - μ₂ = 0 ∧
          μ₁ * (G.a i - s i) = 0 ∧
          μ₂ * (s i - G.b i) = 0) ∧
        (∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < kbar (G.alpha s)), x i =
            G.alpha s 0) ∧
        ∀ i : Fin n, kbar (G.alpha s) ≤ (i : ℕ) → x i = 0) := by
  refine ⟨FR3M.existence G hG, ?_⟩
  intro s x hbox hanti
  have hδpos : ∀ i, 0 < G.δ i (s i) := by
    intro i
    obtain ⟨l, r, hl, hr, hδp, _, _⟩ := hG.δ_regular i
    exact hδp _ ⟨lt_of_lt_of_le hl (hbox i).1.1, lt_of_le_of_lt (hbox i).1.2 hr⟩
  have hαnn : ∀ i, 0 ≤ G.alpha s i := fun i =>
    le_min (div_pos (hG.B_pos i) (mul_pos (hδpos i) (FR3M.theta_pos s i))).le zero_le_one
  have hαle : ∀ i, G.alpha s i ≤ 1 := fun i => min_le_right _ _
  rw [eq_S11 G hG s x hbox, forall_and,
    ← effort_system (G.alpha s) x hanti hαnn hαle (fun i => (hbox i).2)]
  apply and_congr_left'
  exact forall_congr' fun i => FR3M.kkt_iff G hG s i (hbox i).1
