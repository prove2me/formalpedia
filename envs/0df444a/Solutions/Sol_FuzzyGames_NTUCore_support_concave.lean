-- Prove2me | solution 1 for FuzzyGames.NTUCore.support_concave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T20:00:25.006212+00:00
-- url     : https://prove2.me/submissions/1c33d1e6-e120-4125-a8d4-e5d91d4e0353

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore.Aux31
open FuzzyGames.NTUCore

/-- The real-valued support function `sup_{w ∈ W} Σ_i l_i w_i`. -/
noncomputable def rs {n : ℕ} (W : Set (Fin n → ℝ)) (l : Fin n → ℝ) : ℝ :=
  sSup ((fun w => ∑ i, l i * w i) '' W)

section
variable {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)}

theorem bddA (hV : IsNTUFuzzyGame V) {τ : Fin n → ℝ} (hτ : τ ∈ orthant n) {l : Fin n → ℝ}
    (hl : ∀ i, 0 ≤ l i) : BddAbove ((fun w => ∑ i, l i * w i) '' V τ) := by
  obtain ⟨C, _, hC⟩ := hV.bddAbove τ hτ
  refine ⟨∑ i, l i * C i, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨c, hc, p, hp, hcp⟩ := Set.mem_sub.1 (hC hw)
  rw [Set.mem_singleton_iff] at hc
  subst hc
  apply Finset.sum_le_sum; intro i _
  apply mul_le_mul_of_nonneg_left _ (hl i)
  rw [← hcp]; simp only [Pi.sub_apply]; linarith [hp.2 i]

theorem neA (hV : IsNTUFuzzyGame V) {τ : Fin n → ℝ} (hτ : τ ∈ orthant n) (l : Fin n → ℝ) :
    ((fun w => ∑ i, l i * w i) '' V τ).Nonempty :=
  (hV.nonempty τ hτ).image _

theorem le_rs (hV : IsNTUFuzzyGame V) {τ : Fin n → ℝ} (hτ : τ ∈ orthant n) {l : Fin n → ℝ}
    (hl : ∀ i, 0 ≤ l i) {w : Fin n → ℝ} (hw : w ∈ V τ) : ∑ i, l i * w i ≤ rs (V τ) l :=
  le_csSup (bddA hV hτ hl) ⟨w, hw, rfl⟩

theorem rs_le (hV : IsNTUFuzzyGame V) {τ : Fin n → ℝ} (hτ : τ ∈ orthant n) {l : Fin n → ℝ}
    {b : ℝ} (h : ∀ w ∈ V τ, ∑ i, l i * w i ≤ b) : rs (V τ) l ≤ b :=
  csSup_le (neA hV hτ l) (by rintro _ ⟨w, hw, rfl⟩; exact h w hw)

theorem supportFn_eq (hV : IsNTUFuzzyGame V) {τ : Fin n → ℝ} (hτ : τ ∈ orthant n)
    {l : Fin n → ℝ} (hl : ∀ i, 0 ≤ l i) : supportFn (V τ) l = ((rs (V τ) l : ℝ) : EReal) := by
  apply le_antisymm
  · unfold supportFn
    exact iSup₂_le fun w hw => EReal.coe_le_coe_iff.2 (le_rs hV hτ hl hw)
  · by_contra h
    push_neg at h
    obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 h
    rw [EReal.coe_lt_coe_iff] at hb2
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (neA hV hτ l) hb2
    have : ((∑ i, l i * w i : ℝ) : EReal) ≤ supportFn (V τ) l := by
      unfold supportFn
      exact le_iSup₂ (f := fun c (_ : c ∈ V τ) => ((∑ i, l i * c i : ℝ) : EReal)) w hw
    have := this.trans_lt hb1
    rw [EReal.coe_lt_coe_iff] at this
    linarith

theorem cube_orthant {τ : Fin n → ℝ} (hτ : τ ∈ cube n) : τ ∈ orthant n := hτ.1

/-- Separation: if `τ · c` cannot be improved upon by `τ`, some `λ ∈ M^τ` supports it. -/
theorem exists_l (hV : IsNTUFuzzyGame V) {τ c : Fin n → ℝ} (hτ : τ ∈ cube n)
    (hz : tmul τ c ∉ V τ - RtauPos τ) :
    ∃ l ∈ simplexOn τ, ∀ w ∈ V τ, ∑ i, l i * w i ≤ ∑ i, l i * τ i * c i := by
  classical
  have hτ0 : ∀ i, 0 ≤ τ i := fun i => hτ.1 i
  set P : Set (Fin n → ℝ) := {p | ∀ i, 0 < τ i → 0 < p i} with hP_def
  have hPopen : IsOpen P := by
    have : P = ⋂ i, {p : Fin n → ℝ | 0 < τ i → 0 < p i} := by ext p; simp [P]
    rw [this]
    apply isOpen_iInter_of_finite; intro i
    by_cases h : 0 < τ i
    · simp only [h, true_implies]; exact isOpen_lt continuous_const (continuous_apply i)
    · simp [h]
  have hPconv : Convex ℝ P := by
    intro x hx y hy a b ha hb hab i hi
    have hx' := hx i hi; have hy' := hy i hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' hx', mul_nonneg hb hy'.le]
    · subst ha'; simp at hab; subst hab; simpa using hy'
  have hOopen : IsOpen (V τ - P) := hPopen.sub_left
  have hOconv : Convex ℝ (V τ - P) := (hV.convex τ hτ.1).sub hPconv
  have hzO : tmul τ c ∉ V τ - P := by
    rintro ⟨w, hw, p, hp, hzp⟩
    apply hz
    refine ⟨w, hw, p, ⟨fun i hi => ?_, hp⟩, hzp⟩
    have h1 := congrFun hzp i
    have h2 : w i = 0 := hV.subset_Rtau τ hτ.1 hw i hi
    simp only [Pi.sub_apply, tmul, hi, zero_mul] at h1
    linarith
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hOconv hOopen hzO
  set μ : Fin n → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hμ_def
  have hfx : ∀ x : Fin n → ℝ, f x = ∑ i, x i * μ i := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) x
    simpa [μ, smul_eq_mul] using this
  have hmain : ∀ w ∈ V τ, ∀ p ∈ P, ∑ i, (w i - p i) * μ i < ∑ i, tmul τ c i * μ i := by
    intro w hw p hp
    have := hf (w - p) ⟨w, hw, p, hp, rfl⟩
    rw [hfx, hfx] at this; simpa using this
  obtain ⟨w0, hw0⟩ := hV.nonempty τ hτ.1
  set e : Fin n → ℝ := fun i => if 0 < τ i then 1 else 0 with he_def
  have he : e ∈ P := fun i hi => by simp [e, hi]
  set Z := ∑ i, tmul τ c i * μ i with hZ
  set G := ∑ i, (w0 i - e i) * μ i with hG
  -- shifting `p` in coordinate `i`
  have hshift : ∀ i (t : ℝ), (0 < τ i → 0 ≤ t) → G - t * μ i < Z := by
    intro i t ht
    have hp : (fun j => e j + if j = i then t else 0) ∈ P := by
      intro j hj
      by_cases hji : j = i
      · subst hji; simp [e, hj, ht hj]; linarith [ht hj]
      · simp [e, hj, hji]
    have := hmain w0 hw0 _ hp
    have hcalc : ∑ j, (w0 j - (e j + if j = i then t else 0)) * μ j = G - t * μ i := by
      rw [hG]
      have : ∀ j, (w0 j - (e j + if j = i then t else 0)) * μ j
          = (w0 j - e j) * μ j - (if j = i then t * μ i else 0) := by
        intro j; split_ifs with h
        · subst h; ring
        · ring
      simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hcalc] at this; exact this
  have hμpos : ∀ i, 0 < τ i → 0 ≤ μ i := by
    intro i hi
    by_contra hneg; push_neg at hneg
    have := hshift i (max 0 ((Z - G) / (-μ i))) (fun _ => le_max_left _ _)
    have h2 : (Z - G) / (-μ i) ≤ max 0 ((Z - G) / (-μ i)) := le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at h2
    nlinarith
  have hμzero : ∀ i, ¬ 0 < τ i → μ i = 0 := by
    intro i hi
    by_contra hne
    have := hshift i (-(|Z - G| + 1) / μ i) (fun h => absurd h hi)
    have : -(|Z - G| + 1) / μ i * μ i = -(|Z - G| + 1) := div_mul_cancel₀ _ hne
    have := le_abs_self (Z - G)
    linarith
  have hμnn : ∀ i, 0 ≤ μ i := fun i => by
    by_cases h : 0 < τ i
    · exact hμpos i h
    · rw [hμzero i h]
  -- supporting inequality
  have hsupp : ∀ w ∈ V τ, ∑ i, w i * μ i ≤ Z := by
    intro w hw
    by_contra hlt; push_neg at hlt
    set E := ∑ i, e i * μ i with hE
    have hE0 : 0 ≤ E := Finset.sum_nonneg fun i _ => mul_nonneg (by simp only [e]; split_ifs <;> norm_num) (hμnn i)
    set d := ∑ i, w i * μ i - Z
    have hd : 0 < d := by simp only [d]; linarith
    set ε := d / (E + 1)
    have hε : 0 < ε := div_pos hd (by linarith)
    have hp : ε • e ∈ P := fun i hi => by simp [e, hi, hε]
    have h1 := hmain w hw _ hp
    have h2 : ∑ i, (w i - (ε • e) i) * μ i = ∑ i, w i * μ i - ε * E := by
      rw [hE, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [h2] at h1
    have h3 : ε * E < d := by
      have : ε * (E + 1) = d := div_mul_cancel₀ _ (by linarith)
      nlinarith
    simp only [d] at h3
    linarith
  set S := ∑ i, μ i with hS
  have hSpos : 0 < S := by
    rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hμnn i).lt_or_eq with h | h
    · exact h
    · exfalso
      have hall : ∀ i, μ i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hμnn j)).1 h.symm i (Finset.mem_univ i)
      have h1 := hmain w0 hw0 e he
      have h2 : ∑ i, (w0 i - e i) * μ i = 0 := Finset.sum_eq_zero fun i _ => by rw [hall i, mul_zero]
      have h3 : Z = 0 := by rw [hZ]; exact Finset.sum_eq_zero fun i _ => by rw [hall i, mul_zero]
      linarith
  refine ⟨fun i => μ i / S, ⟨⟨fun i hi => ?_, fun i => div_nonneg (hμnn i) hSpos.le⟩, ?_⟩, ?_⟩
  · have : ¬ 0 < τ i := by rw [hi]; exact lt_irrefl 0
    simp [hμzero i this]
  · rw [← Finset.sum_div, div_self hSpos.ne']
  · intro w hw
    have h1 := hsupp w hw
    have e1 : ∑ i, μ i / S * w i = (∑ i, w i * μ i) / S := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring
    have e2 : ∑ i, μ i / S * τ i * c i = Z / S := by
      rw [hZ, Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; simp only [tmul]; ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right h1 hSpos.le


theorem rs_concave (hV : IsNTUFuzzyGame V) (hsup : Superadditive V) {τ₁ τ₂ : Fin n → ℝ}
    (h1 : τ₁ ∈ orthant n) (h2 : τ₂ ∈ orthant n) {l : Fin n → ℝ} (hl : ∀ i, 0 ≤ l i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * rs (V τ₁) l + (1 - t) * rs (V τ₂) l ≤ rs (V (t • τ₁ + (1 - t) • τ₂)) l := by
  rcases ht0.lt_or_eq with ht0' | ht0'
  · rcases ht1.lt_or_eq with ht1' | ht1'
    · have hs : 0 < 1 - t := by linarith
      have ho1 : t • τ₁ ∈ orthant n := fun i => by
        simpa using mul_nonneg ht0 (h1 i)
      have ho2 : (1 - t) • τ₂ ∈ orthant n := fun i => by
        simpa using mul_nonneg hs.le (h2 i)
      have ho : t • τ₁ + (1 - t) • τ₂ ∈ orthant n := fun i => by
        simpa using add_nonneg (ho1 i) (ho2 i)
      set R := rs (V (t • τ₁ + (1 - t) • τ₂)) l
      have key : ∀ w ∈ V τ₁, ∀ u ∈ V τ₂,
          t * ∑ i, l i * w i + (1 - t) * ∑ i, l i * u i ≤ R := by
        intro w hw u hu
        have hmem : t • w + (1 - t) • u ∈ V (t • τ₁ + (1 - t) • τ₂) := by
          apply hsup _ ho1 _ ho2
          refine Set.add_mem_add ?_ ?_
          · rw [hV.homogeneous t ht0' τ₁ h1]; exact Set.smul_mem_smul_set hw
          · rw [hV.homogeneous (1 - t) hs τ₂ h2]; exact Set.smul_mem_smul_set hu
        have := le_rs hV ho hl hmem
        have e : ∑ i, l i * (t • w + (1 - t) • u) i =
            t * ∑ i, l i * w i + (1 - t) * ∑ i, l i * u i := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _; ring
        linarith
      have step1 : ∀ u ∈ V τ₂, t * rs (V τ₁) l + (1 - t) * ∑ i, l i * u i ≤ R := by
        intro u hu
        have : rs (V τ₁) l ≤ (R - (1 - t) * ∑ i, l i * u i) / t := by
          apply rs_le hV h1
          intro w hw
          rw [le_div_iff₀ ht0']
          linarith [key w hw u hu]
        rw [le_div_iff₀ ht0'] at this
        linarith
      have : rs (V τ₂) l ≤ (R - t * rs (V τ₁) l) / (1 - t) := by
        apply rs_le hV h2
        intro u hu
        rw [le_div_iff₀ hs]
        linarith [step1 u hu]
      rw [le_div_iff₀ hs] at this
      linarith
    · subst ht1'; simp
  · subst ht0'; simp

end

end FuzzyGames.NTUCore.Aux31

open FuzzyGames.NTUCore FuzzyGames.NTUCore.Aux31 in
theorem solution {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)} (hV : IsNTUFuzzyGame V)
    (hsup : Superadditive V) {l : Fin n → ℝ} (hl : ∀ i, 0 ≤ l i) :
    (∀ τ ∈ orthant n, ∃ r : ℝ, supportFn (V τ) l = (r : EReal)) ∧
      ConcaveOn ℝ (orthant n) (fun τ => (supportFn (V τ) l).toReal) := by
  refine ⟨fun τ hτ => ⟨_, supportFn_eq hV hτ hl⟩, convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ orthant n := (convex_Ici (0 : Fin n → ℝ)) hx hy ha hb hab
  simp only [supportFn_eq hV hx hl, supportFn_eq hV hy hl, supportFn_eq hV hxy hl,
    EReal.toReal_coe, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  exact rs_concave hV hsup hx hy hl ha (by linarith)
