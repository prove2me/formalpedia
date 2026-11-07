-- Prove2me | solution 1 for FuzzyGames.NTUCore.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:58:03.052224+00:00
-- url     : https://prove2.me/submissions/02a59ccb-5080-4a60-84ef-4d9705ffa0b6

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic
import Theorems.Thm_SionMinimax_KneserFan_theorem_4_2_prime

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

theorem rs_convex (hV : IsNTUFuzzyGame V) {τ : Fin n → ℝ} (hτ : τ ∈ orthant n)
    {l₁ l₂ : Fin n → ℝ} (hl₁ : ∀ i, 0 ≤ l₁ i) (hl₂ : ∀ i, 0 ≤ l₂ i) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    rs (V τ) (t • l₁ + (1 - t) • l₂) ≤ t * rs (V τ) l₁ + (1 - t) * rs (V τ) l₂ := by
  apply rs_le hV hτ
  intro w hw
  have e : ∑ i, (t • l₁ + (1 - t) • l₂) i * w i =
      t * ∑ i, l₁ i * w i + (1 - t) * ∑ i, l₂ i * w i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [e]
  have a1 := le_rs hV hτ hl₁ hw
  have a2 := le_rs hV hτ hl₂ hw
  have : 0 ≤ 1 - t := by linarith
  nlinarith

theorem simplex_univ_iff {l : Fin n → ℝ} :
    l ∈ simplexOn (coal (Finset.univ : Finset (Fin n))) ↔ (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1 := by
  simp only [simplexOn, RtauNonneg, Rtau, coal, Finset.mem_univ, if_true, one_ne_zero,
    false_implies, implies_true, true_and, Set.mem_setOf_eq]

theorem simplex_univ_compact :
    IsCompact (simplexOn (coal (Finset.univ : Finset (Fin n)))) := by
  have hset : simplexOn (coal (Finset.univ : Finset (Fin n))) =
      Set.Ici 0 ∩ {l : Fin n → ℝ | ∑ i, l i = 1} := by
    ext l; rw [simplex_univ_iff]; simp [Pi.le_def]
  rw [hset]
  apply (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := 1)).of_isClosed_subset
  · exact isClosed_Ici.inter (isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i)
      continuous_const)
  · rintro l ⟨h0, h1⟩
    refine ⟨h0, fun i => ?_⟩
    have : l i ≤ ∑ j, l j :=
      Finset.single_le_sum (f := l) (fun j _ => h0 j) (Finset.mem_univ i)
    simp only [Set.mem_setOf_eq] at h1
    simp only [Pi.one_apply]; linarith

end

end FuzzyGames.NTUCore.Aux31

open FuzzyGames.NTUCore FuzzyGames.NTUCore.Aux31 SionMinimax.KneserFan in
theorem solution {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)} (hV : IsNTUFuzzyGame V) :
    strongCCE V ⊆ fuzzyCore V ∧
      (Superadditive V → 0 < n → fuzzyCore V ⊆ weakCCE V) := by
  classical
  constructor
  · -- (a)
    rintro c ⟨hc, l, hlS, hle⟩
    have hlpos := hlS.2.2
    refine ⟨hc, fun τ hτ hne hmem => ?_⟩
    obtain ⟨w, hw, p, hp, hwp⟩ := Set.mem_sub.1 hmem
    have hlp : ∀ i, 0 < l i := fun i => hlpos i (by simp [coal])
    have hp0 : ∀ i, 0 ≤ p i := fun i => by
      rcases (hτ.1 i).lt_or_eq with h | h
      · exact (hp.2 i h).le
      · rw [hp.1 i h.symm]
    obtain ⟨j, hj⟩ : ∃ j, 0 < τ j := by
      by_contra hcon; push_neg at hcon
      exact hne (funext fun i => le_antisymm (hcon i) (hτ.1 i))
    have hpos : 0 < ∑ i, l i * p i :=
      Finset.sum_pos' (fun i _ => mul_nonneg (hlp i).le (hp0 i))
        ⟨j, Finset.mem_univ j, mul_pos (hlp j) (hp.2 j hj)⟩
    have h1 : ((∑ i, l i * w i : ℝ) : EReal) ≤ supportFn (V τ) l := by
      unfold supportFn
      exact le_iSup₂ (f := fun c (_ : c ∈ V τ) => ((∑ i, l i * c i : ℝ) : EReal)) w hw
    have h2 := (h1.trans (hle τ hτ))
    rw [EReal.coe_le_coe_iff] at h2
    have e : ∑ i, l i * w i = ∑ i, l i * τ i * c i + ∑ i, l i * p i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      have := congrFun hwp i
      simp only [Pi.sub_apply, tmul] at this
      have : w i = τ i * c i + p i := by linarith
      rw [this]; ring
    linarith
  · -- (b)
    intro hsup hn c hcore
    obtain ⟨hc, hcore⟩ := hcore
    let M := {τ : Fin n → ℝ // τ ∈ cube n}
    let N := {l : Fin n → ℝ // l ∈ simplexOn (coal (Finset.univ : Finset (Fin n)))}
    haveI : CompactSpace N := isCompact_iff_compactSpace.1 simplex_univ_compact
    have hNnn : ∀ ν : N, ∀ i, 0 ≤ ν.1 i := fun ν => (simplex_univ_iff.1 ν.2).1
    let f : M → N → ℝ := fun τ ν => rs (V τ.1) ν.1 - ∑ i, ν.1 i * τ.1 i * c i
    have hconc : Concavelike f := by
      intro τ₁ τ₂ t ht0 ht1
      have hmem : t • τ₁.1 + (1 - t) • τ₂.1 ∈ cube n :=
        (convex_Icc (0 : Fin n → ℝ) 1) τ₁.2 τ₂.2 ht0 (by linarith) (by ring)
      refine ⟨⟨_, hmem⟩, fun ν => ?_⟩
      have := rs_concave hV hsup τ₁.2.1 τ₂.2.1 (hNnn ν) ht0 ht1
      have e : ∑ i, ν.1 i * (t • τ₁.1 + (1 - t) • τ₂.1) i * c i =
          t * ∑ i, ν.1 i * τ₁.1 i * c i + (1 - t) * ∑ i, ν.1 i * τ₂.1 i * c i := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      simp only [f, e]
      linarith
    have hconv : Convexlike f := by
      intro ν₁ ν₂ t ht0 ht1
      have hmem : t • ν₁.1 + (1 - t) • ν₂.1 ∈ simplexOn (coal (Finset.univ : Finset (Fin n))) := by
        rw [simplex_univ_iff]
        obtain ⟨a0, a1⟩ := simplex_univ_iff.1 ν₁.2
        obtain ⟨b0, b1⟩ := simplex_univ_iff.1 ν₂.2
        refine ⟨fun i => ?_, ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have := a0 i; have := b0 i
          have : 0 ≤ 1 - t := by linarith
          positivity
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum, a1, b1]; ring
      refine ⟨⟨_, hmem⟩, fun τ => ?_⟩
      have := rs_convex hV τ.2.1 (hNnn ν₁) (hNnn ν₂) ht0 ht1
      have e : ∑ i, (t • ν₁.1 + (1 - t) • ν₂.1) i * τ.1 i * c i =
          t * ∑ i, ν₁.1 i * τ.1 i * c i + (1 - t) * ∑ i, ν₂.1 i * τ.1 i * c i := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      simp only [f, e]
      linarith
    have hlsc : ∀ τ : M, LowerSemicontinuous (fun ν : N => f τ ν) := by
      intro τ ν y hy
      simp only [f] at hy
      have hy' : y + ∑ i, ν.1 i * τ.1 i * c i < rs (V τ.1) ν.1 := by linarith
      obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (neA hV τ.2.1 ν.1) hy'
      have hcont : Continuous fun ν' : N => ∑ i, ν'.1 i * w i - ∑ i, ν'.1 i * τ.1 i * c i :=
        (continuous_finset_sum _ fun i _ =>
          ((continuous_apply i).comp continuous_subtype_val).mul continuous_const).sub
        (continuous_finset_sum _ fun i _ =>
          (((continuous_apply i).comp continuous_subtype_val).mul continuous_const).mul
            continuous_const)
      have h0 : y < ∑ i, ν.1 i * w i - ∑ i, ν.1 i * τ.1 i * c i := by linarith
      filter_upwards [(hcont.tendsto ν).eventually (lt_mem_nhds h0)] with ν' hν'
      have := le_rs hV τ.2.1 (hNnn ν') hw
      simp only [f]
      linarith
    have hminimax := theorem_4_2_prime f ⟨hconc, hconv⟩
      (Or.inl ⟨⟨0, ⟨le_rfl, zero_le_one⟩⟩⟩) hlsc
    -- uniform element of N
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    let ν₀ : N := ⟨fun _ => 1 / n, simplex_univ_iff.2 ⟨fun _ => by positivity, by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp⟩⟩
    have hsupinf : supInf f ≤ 0 := by
      unfold supInf
      refine iSup_le fun τ => ?_
      by_cases hτ0 : τ.1 = 0
      · refine iInf_le_of_le ν₀ ?_
        rw [EReal.coe_nonpos]
        simp only [f]
        have : rs (V τ.1) ν₀.1 ≤ 0 := by
          apply rs_le hV τ.2.1
          intro w hw
          have hw0 : ∀ i, w i = 0 := fun i => hV.subset_Rtau τ.1 τ.2.1 hw i (by rw [hτ0]; rfl)
          simp [hw0]
        have h2 : ∑ i, ν₀.1 i * τ.1 i * c i = 0 := by simp [hτ0]
        linarith
      · obtain ⟨l, hl, hlw⟩ := exists_l hV τ.2 (hcore τ.1 τ.2 hτ0)
        have hlN : l ∈ simplexOn (coal (Finset.univ : Finset (Fin n))) :=
          simplex_univ_iff.2 ⟨hl.1.2, hl.2⟩
        refine iInf_le_of_le ⟨l, hlN⟩ ?_
        rw [EReal.coe_nonpos]
        simp only [f]
        have := rs_le hV τ.2.1 hlw
        linarith
    have hinfsup : infSup f ≤ 0 := hminimax ▸ hsupinf
    haveI : Nonempty N := ⟨ν₀⟩
    let g : N → EReal := fun ν => ⨆ τ : M, ((f τ ν : ℝ) : EReal)
    have hg : LowerSemicontinuous g := lowerSemicontinuous_iSup fun τ =>
      continuous_coe_real_ereal.comp_lowerSemicontinuous (hlsc τ)
        (fun a b h => EReal.coe_le_coe_iff.2 h)
    obtain ⟨ν', -, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (s := Set.univ)
      Set.univ_nonempty isCompact_univ (hg.lowerSemicontinuousOn Set.univ)
    have hgν : g ν' ≤ 0 := by
      refine le_trans ?_ hinfsup
      unfold infSup
      exact le_iInf fun ν => (hmin (Set.mem_univ ν) : g ν' ≤ g ν)
    refine ⟨hc, ν'.1, ν'.2, fun τ hτ => ?_⟩
    have h1 : ((f ⟨τ, hτ⟩ ν' : ℝ) : EReal) ≤ 0 :=
      (le_iSup (fun τ : M => ((f τ ν' : ℝ) : EReal)) ⟨τ, hτ⟩).trans hgν
    rw [EReal.coe_nonpos] at h1
    simp only [f] at h1
    rw [supportFn_eq hV hτ.1 (hNnn ν'), EReal.coe_le_coe_iff]
    linarith
