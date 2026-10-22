-- Prove2me | solution 1 for ConfoundRobust.Minimax.corollary_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:16:36.179453+00:00
-- url     : https://prove2.me/submissions/20e56143-158b-48d4-bb93-4bc207d382dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting
import Theorems.Thm_ConfoundRobust_Minimax_proposition_3

open MeasureTheory

namespace CR4Aux
open ConfoundRobust.Minimax

/-- Abstract form of the argument: if the supremum over `A` of `∑ₛ f s` equals the sum of the
per-coordinate suprema over `Bs`, and `A` is closed under gluing coordinates, then any `C` with
`Bs ⊆ C ⊆ A` has the same per-coordinate suprema. -/
theorem abs_sup {α : Type*} {m : ℕ} (A Bs C : Set α) (f : Fin m → α → ℝ) (M : ℝ)
    (hBA : Bs ⊆ A) (hBC : Bs ⊆ C) (hCA : C ⊆ A) (hBne : Bs.Nonempty)
    (hM : ∀ s, ∀ W ∈ A, f s W ≤ M)
    (hglue : ∀ t, ∀ W ∈ A, ∀ V : Fin m → α, (∀ s, V s ∈ A) →
      ∃ W' ∈ A, ∀ s, f s W' = if s = t then f t W else f s (V s))
    (hP3 : sSup ((fun W => ∑ s, f s W) '' A) = ∑ s, sSup (f s '' Bs)) :
    sSup ((fun W => ∑ s, f s W) '' A) = ∑ s, sSup (f s '' C) := by
  rw [hP3]
  have hbddA : BddAbove ((fun W => ∑ s, f s W) '' A) := by
    refine ⟨∑ _s : Fin m, M, ?_⟩
    rintro _ ⟨W, hW, rfl⟩
    exact Finset.sum_le_sum (fun s _ => hM s W hW)
  have key : ∀ t, ∀ W ∈ A, f t W ≤ sSup (f t '' Bs) := by
    intro t W hW
    by_contra hcon
    push Not at hcon
    set S : Fin m → ℝ := fun s => sSup (f s '' Bs) with hS
    set d := f t W - S t with hd
    have hdpos : 0 < d := by simp only [hd, hS]; linarith
    set ε := d / ((m : ℝ) + 1) with hε
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hεpos : 0 < ε := div_pos hdpos hm1
    have hmε : (m : ℝ) * ε < d := by
      rw [hε, mul_div_assoc', div_lt_iff₀ hm1]; nlinarith
    have hV : ∀ s, ∃ V ∈ Bs, S s - ε < f s V := by
      intro s
      obtain ⟨_, ⟨V, hV, rfl⟩, hlt⟩ :=
        exists_lt_of_lt_csSup (hBne.image (f s)) (show S s - ε < S s by linarith)
      exact ⟨V, hV, hlt⟩
    choose V hVB hVlt using hV
    obtain ⟨W', hW'A, hW'⟩ := hglue t W hW V (fun s => hBA (hVB s))
    have hle : ∑ s, f s W' ≤ ∑ s, S s := by
      exact (le_csSup hbddA ⟨W', hW'A, rfl⟩).trans hP3.le
    have hge : ∑ s, (S s - ε + (if s = t then f t W - S t + ε else 0)) ≤ ∑ s, f s W' := by
      apply Finset.sum_le_sum
      intro s _
      rw [hW' s]
      by_cases hst : s = t
      · subst hst; simp
      · simp [hst]; linarith [hVlt s]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ t, Finset.sum_sub_distrib] at hge
    simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hge
    linarith
  refine Finset.sum_congr rfl (fun t _ => ?_)
  apply le_antisymm
  · apply csSup_le_csSup ⟨M, ?_⟩ (hBne.image _) (Set.image_mono hBC)
    rintro _ ⟨W, hW, rfl⟩
    exact hM t W (hCA hW)
  · apply csSup_le ((hBne.mono hBC).image _)
    rintro _ ⟨W, hW, rfl⟩
    exact key t W (hCA hW)

variable {𝒳 : Type} [MeasurableSpace 𝒳] {m : ℕ}

theorem meas_sel (g : Fin m → Obs 𝒳 m → ℝ) (hg : ∀ s, Measurable (g s)) :
    Measurable (fun z : Obs 𝒳 m => g z.2.1 z) := by
  have heq : (fun z : Obs 𝒳 m => g z.2.1 z) =
      fun z => ∑ s, if z.2.1 = s then g s z else 0 := by
    funext z
    rw [Finset.sum_ite_eq]; simp
  rw [heq]
  refine Finset.measurable_sum _ (fun s _ => ?_)
  refine Measurable.ite ?_ (hg s) measurable_const
  exact measurable_snd.fst (measurableSet_singleton s)

theorem pol_le_one {π : 𝒳 → Fin m → ℝ} (hπ : IsPolicy π) (x : 𝒳) (t : Fin m) : π x t ≤ 1 := by
  have h := (hπ.2 x).2
  rw [← h]
  exact Finset.single_le_sum (fun s _ => (hπ.2 x).1 s) (Finset.mem_univ t)

theorem pol_diff_abs {π π0 : 𝒳 → Fin m → ℝ} (hπ : IsPolicy π) (hπ0 : IsPolicy π0) (x : 𝒳)
    (t : Fin m) : |π x t - π0 x t| ≤ 1 := by
  have a := (hπ.2 x).1 t; have b := (hπ0.2 x).1 t
  have c := pol_le_one hπ x t; have d := pol_le_one hπ0 x t
  rw [abs_le]; constructor <;> linarith

section bounds
variable {Γ ν : ℝ} {e : Fin m → 𝒳 → ℝ}

theorem one_le_aG (hν : 0 < ν) (heν : ∀ t x, ν ≤ e t x) (he1 : ∀ t x, e t x ≤ 1) (hΓ : 1 ≤ Γ)
    (t : Fin m) (x : 𝒳) : 1 ≤ aG Γ e t x := by
  unfold aG
  have hpos : 0 < e t x := lt_of_lt_of_le hν (heν t x)
  have h1 : 1 ≤ 1 / e t x := by rw [le_div_iff₀ hpos]; linarith [he1 t x]
  have : 0 ≤ Γ⁻¹ * (1 / e t x - 1) := mul_nonneg (by positivity) (by linarith)
  linarith

theorem aG_le_bG (hν : 0 < ν) (heν : ∀ t x, ν ≤ e t x) (he1 : ∀ t x, e t x ≤ 1) (hΓ : 1 ≤ Γ)
    (t : Fin m) (x : 𝒳) : aG Γ e t x ≤ bG Γ e t x := by
  unfold aG bG
  have hpos : 0 < e t x := lt_of_lt_of_le hν (heν t x)
  have h1 : 1 ≤ 1 / e t x := by rw [le_div_iff₀ hpos]; linarith [he1 t x]
  have hg : Γ⁻¹ ≤ Γ := by
    have : Γ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΓ
    linarith
  nlinarith

theorem bG_le (hν : 0 < ν) (heν : ∀ t x, ν ≤ e t x) (hΓ : 1 ≤ Γ)
    (t : Fin m) (x : 𝒳) : bG Γ e t x ≤ 1 + Γ * (1 / ν - 1) := by
  unfold bG
  have hpos : 0 < e t x := lt_of_lt_of_le hν (heν t x)
  have h1 : 1 / e t x ≤ 1 / ν := one_div_le_one_div_of_le hν (heν t x)
  nlinarith

theorem meas_aG (he : ∀ t, Measurable (e t)) :
    Measurable (fun z : Obs 𝒳 m => aG Γ e z.2.1 z.1) := by
  apply meas_sel (fun s z => aG Γ e s z.1)
  intro s
  unfold aG
  have : Measurable (fun z : Obs 𝒳 m => e s z.1) := (he s).comp measurable_fst
  fun_prop

theorem meas_bG (he : ∀ t, Measurable (e t)) :
    Measurable (fun z : Obs 𝒳 m => bG Γ e z.2.1 z.1) := by
  apply meas_sel (fun s z => bG Γ e s z.1)
  intro s
  unfold bG
  have : Measurable (fun z : Obs 𝒳 m => e s z.1) := (he s).comp measurable_fst
  fun_prop

theorem meas_score {π π0 : 𝒳 → Fin m → ℝ} (hπ : IsPolicy π) (hπ0 : IsPolicy π0) :
    Measurable (score π π0) := by
  unfold score
  have h1 : Measurable (fun z : Obs 𝒳 m => π z.1 z.2.1) :=
    meas_sel (fun s z => π z.1 s) (fun s => (hπ.1 s).comp measurable_fst)
  have h2 : Measurable (fun z : Obs 𝒳 m => π0 z.1 z.2.1) :=
    meas_sel (fun s z => π0 z.1 s) (fun s => (hπ0.1 s).comp measurable_fst)
  exact measurable_snd.snd.mul (h1.sub h2)

theorem wbar_sub (hem : ∀ t, Measurable (e t))
    (hν : 0 < ν) (heν : ∀ t x, ν ≤ e t x) (he1 : ∀ t x, e t x ≤ 1) (hΓ : 1 ≤ Γ)
    {π π0 : 𝒳 → Fin m → ℝ} (hπ : IsPolicy π) (hπ0 : IsPolicy π0) :
    WbarSet Γ e π π0 ⊆ WSet Γ e := by
  rintro W ⟨u, hu, hW⟩
  have hWeq : W = fun z => aG Γ e z.2.1 z.1 + u (score π π0 z) * (bG Γ e z.2.1 z.1 - aG Γ e z.2.1 z.1) :=
    funext hW
  refine ⟨?_, fun z => ?_⟩
  · rw [hWeq]
    have hum : Measurable u := hu.1.measurable
    exact (meas_aG hem).add ((hum.comp (meas_score hπ hπ0)).mul ((meas_bG hem).sub (meas_aG hem)))
  · rw [hW z]
    have hab := aG_le_bG hν heν he1 hΓ z.2.1 z.1
    have h0 := (hu.2 (score π π0 z)).1
    have h1 := (hu.2 (score π π0 z)).2
    constructor <;> nlinarith

theorem wbar_nonempty {π π0 : 𝒳 → Fin m → ℝ} : (WbarSet Γ e π π0).Nonempty :=
  ⟨fun z => aG Γ e z.2.1 z.1 + (fun _ => (0 : ℝ)) (score π π0 z) *
      (bG Γ e z.2.1 z.1 - aG Γ e z.2.1 z.1),
    fun _ => 0, ⟨monotone_const, fun _ => ⟨le_refl _, zero_le_one⟩⟩, fun _ => rfl⟩

end bounds

theorem regretT_congr (μ : Measure (Obs 𝒳 m)) (π π0 : 𝒳 → Fin m → ℝ) (W W' : Obs 𝒳 m → ℝ)
    (t : Fin m) (h : ∀ z : Obs 𝒳 m, z.2.1 = t → W z = W' z) :
    regretT μ π π0 W t = regretT μ π π0 W' t := by
  have h1 : (fun z : Obs 𝒳 m => if z.2.1 = t then (π z.1 t - π0 z.1 t) * W z * z.2.2 else 0) =
      (fun z => if z.2.1 = t then (π z.1 t - π0 z.1 t) * W' z * z.2.2 else 0) := by
    funext z; split_ifs with hz
    · rw [h z hz]
    · rfl
  have h2 : (fun z : Obs 𝒳 m => if z.2.1 = t then W z else 0) =
      (fun z => if z.2.1 = t then W' z else 0) := by
    funext z; split_ifs with hz
    · rw [h z hz]
    · rfl
  unfold regretT; rw [h1, h2]

theorem sRegretT_congr {n : ℕ} (ω : Fin n → Obs 𝒳 m) (π π0 : 𝒳 → Fin m → ℝ) (w w' : Fin n → ℝ)
    (t : Fin m) (h : ∀ i, (ω i).2.1 = t → w i = w' i) :
    sRegretT ω π π0 w t = sRegretT ω π π0 w' t := by
  unfold sRegretT
  congr 2
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with hi
    · rw [h i hi]
    · rfl
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with hi
    · rw [h i hi]
    · rfl

theorem regretT_abs_le (μ : Measure (Obs 𝒳 m)) [IsProbabilityMeasure μ]
    {π π0 : 𝒳 → Fin m → ℝ} (hπ : IsPolicy π) (hπ0 : IsPolicy π0)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ᵐ z ∂μ, |z.2.2| ≤ B)
    (W : Obs 𝒳 m → ℝ) (hWm : Measurable W) (hW0 : ∀ z, 0 ≤ W z) (Cb : ℝ) (hWC : ∀ z, W z ≤ Cb)
    (t : Fin m) : |regretT μ π π0 W t| ≤ B := by
  unfold regretT
  set g : Obs 𝒳 m → ℝ := fun z => if z.2.1 = t then W z else 0 with hg
  have hset : MeasurableSet {z : Obs 𝒳 m | z.2.1 = t} :=
    measurable_snd.fst (measurableSet_singleton t)
  have hgm : Measurable g := Measurable.ite hset hWm measurable_const
  have hg0 : ∀ z, 0 ≤ g z := by intro z; simp only [hg]; split_ifs <;> simp [hW0]
  have hgint : Integrable g μ := by
    refine Integrable.of_bound hgm.aestronglyMeasurable Cb (Filter.Eventually.of_forall ?_)
    intro z; simp only [hg, Real.norm_eq_abs]
    split_ifs
    · rw [abs_of_nonneg (hW0 z)]; exact hWC z
    · simp; linarith [hW0 z, hWC z]
  have hD : 0 ≤ ∫ z, g z ∂μ := integral_nonneg hg0
  have hN : |∫ z, (if z.2.1 = t then (π z.1 t - π0 z.1 t) * W z * z.2.2 else 0) ∂μ| ≤
      B * ∫ z, g z ∂μ := by
    rw [← integral_const_mul]
    have := norm_integral_le_of_norm_le (μ := μ)
      (f := fun z : Obs 𝒳 m => if z.2.1 = t then (π z.1 t - π0 z.1 t) * W z * z.2.2 else 0)
      (hgint.const_mul B) (by
        filter_upwards [hB] with z hz
        simp only [hg, Real.norm_eq_abs]
        split_ifs
        · rw [abs_mul, abs_mul, abs_of_nonneg (hW0 z)]
          have h1 := pol_diff_abs hπ hπ0 z.1 t
          have h2 := abs_nonneg (π z.1 t - π0 z.1 t)
          have h3 := hW0 z
          have h4 := abs_nonneg z.2.2
          calc |π z.1 t - π0 z.1 t| * W z * |z.2.2| ≤ 1 * W z * B := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right h1 h3) hz h4 (by positivity)
            _ = B * W z := by ring
        · simp)
    simpa [Real.norm_eq_abs] using this
  rcases hD.lt_or_eq with hDp | hD0
  · rw [abs_div, abs_of_pos hDp, div_le_iff₀ hDp]; exact hN
  · rw [← hD0]; simp [hB0]

theorem sRegretT_abs_le {n : ℕ} (ω : Fin n → Obs 𝒳 m) {π π0 : 𝒳 → Fin m → ℝ}
    (hπ : IsPolicy π) (hπ0 : IsPolicy π0) (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (t : Fin m) :
    |sRegretT ω π π0 w t| ≤ ∑ i, |(ω i).2.2| := by
  unfold sRegretT
  set M := ∑ i, |(ω i).2.2| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hc : 0 ≤ (n : ℝ)⁻¹ := by positivity
  set D := (n : ℝ)⁻¹ * ∑ i, (if (ω i).2.1 = t then w i else 0) with hDdef
  have hD : 0 ≤ D := mul_nonneg hc (Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hw0]))
  have hN : |(n : ℝ)⁻¹ * ∑ i, (if (ω i).2.1 = t then (π (ω i).1 t - π0 (ω i).1 t) * (ω i).2.2 * w i
      else 0)| ≤ M * D := by
    rw [abs_mul, abs_of_nonneg hc, hDdef, mul_left_comm, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hc
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    split_ifs
    · rw [abs_mul, abs_mul, abs_of_nonneg (hw0 i)]
      have h1 := pol_diff_abs hπ hπ0 (ω i).1 t
      have hyM : |(ω i).2.2| ≤ M :=
        Finset.single_le_sum (f := fun i => |(ω i).2.2|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
      calc |π (ω i).1 t - π0 (ω i).1 t| * |(ω i).2.2| * w i ≤ 1 * M * w i := by
            apply mul_le_mul_of_nonneg_right _ (hw0 i)
            exact mul_le_mul h1 hyM (abs_nonneg _) zero_le_one
        _ = M * w i := by ring
    · simp
  rcases hD.lt_or_eq with hDp | hD0
  · rw [abs_div, abs_of_pos hDp, div_le_iff₀ hDp]; exact hN
  · rw [← hD0]; simp [hM0]

end CR4Aux

open ConfoundRobust.Minimax CR4Aux in
theorem solution {𝒳 : Type} [MeasurableSpace 𝒳] (m : ℕ) (hm : 2 ≤ m)
    (μ : Measure (Obs 𝒳 m)) [IsProbabilityMeasure μ]
    (e : Fin m → 𝒳 → ℝ) (he : IsNominalPropensity μ e) (ν : ℝ) (hν : 0 < ν)
    (heν : ∀ t x, ν ≤ e t x) (he1 : ∀ t x, e t x ≤ 1)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ᵐ z ∂μ, |z.2.2| ≤ B)
    (Γ : ℝ) (hΓ : 1 ≤ Γ)
    (Pol : Set (𝒳 → Fin m → ℝ)) (hPol : ∀ π ∈ Pol, IsPolicy π)
    (π0 : 𝒳 → Fin m → ℝ) (hπ0 : IsPolicy π0)
    (π : 𝒳 → Fin m → ℝ) (hπPol : π ∈ Pol) :
    worstRegret μ π π0 (WSet Γ e) =
        ∑ t, sSup ((fun W => regretT μ π π0 W t) '' (⋃ π' ∈ Pol, WbarSet Γ e π' π0)) ∧
      ∀ (n : ℕ) (ω : Fin n → Obs 𝒳 m),
        sWorstRegret ω π π0 (WSetN Γ e ω) =
          ∑ t, sSup ((fun w => sRegretT ω π π0 w t) '' (⋃ π' ∈ Pol, WbarSetN Γ e π' π0 ω)) := by
  have hπ : IsPolicy π := hPol π hπPol
  obtain ⟨hP3a, hP3b⟩ :=
    ConfoundRobust.Minimax.proposition_3 m hm μ e he ν hν heν he1 B hB0 hB Γ hΓ π0 hπ0 π hπ
  have hsub : ∀ π' ∈ Pol, WbarSet Γ e π' π0 ⊆ WSet Γ e := fun π' hπ' =>
    wbar_sub he.1 hν heν he1 hΓ (hPol π' hπ') hπ0
  have hW0 : ∀ W ∈ WSet Γ e, ∀ z, 0 ≤ W z := fun W hW z =>
    le_trans (by linarith [one_le_aG hν heν he1 hΓ z.2.1 z.1]) (hW.2 z).1
  constructor
  · refine abs_sup (WSet Γ e) (WbarSet Γ e π π0) (⋃ π' ∈ Pol, WbarSet Γ e π' π0)
      (fun s W => regretT μ π π0 W s) B (hsub π hπPol)
      (Set.subset_biUnion_of_mem (u := fun π' => WbarSet Γ e π' π0) hπPol)
      (Set.iUnion₂_subset hsub) wbar_nonempty ?_ ?_ hP3a
    · intro s W hW
      exact (le_abs_self _).trans (regretT_abs_le μ hπ hπ0 B hB0 hB W hW.1 (hW0 W hW)
        (1 + Γ * (1 / ν - 1)) (fun z => (hW.2 z).2.trans (bG_le hν heν hΓ z.2.1 z.1)) s)
    · intro t W hW V hV
      refine ⟨fun z => if z.2.1 = t then W z else V z.2.1 z, ⟨?_, fun z => ?_⟩, fun s => ?_⟩
      · exact Measurable.ite (measurable_snd.fst (measurableSet_singleton t)) hW.1
          (meas_sel V (fun s => (hV s).1))
      · dsimp only; split_ifs
        · exact hW.2 z
        · exact (hV _).2 z
      · by_cases hst : s = t
        · subst hst; simp only [if_true]
          exact regretT_congr μ π π0 _ _ s (fun z hz => by simp [hz])
        · simp only [hst, if_false]
          exact regretT_congr μ π π0 _ _ s (fun z hz => by simp [hz, hst])
  · intro n ω
    have hsubN : ∀ π' ∈ Pol, WbarSetN Γ e π' π0 ω ⊆ WSetN Γ e ω := by
      intro π' hπ'
      rintro _ ⟨W, hW, rfl⟩ i
      exact (hsub π' hπ' hW).2 (ω i)
    have hw0 : ∀ w ∈ WSetN Γ e ω, ∀ i, 0 ≤ w i := fun w hw i =>
      le_trans (by linarith [one_le_aG hν heν he1 hΓ (ω i).2.1 (ω i).1]) (hw i).1
    refine abs_sup (WSetN Γ e ω) (WbarSetN Γ e π π0 ω) (⋃ π' ∈ Pol, WbarSetN Γ e π' π0 ω)
      (fun s w => sRegretT ω π π0 w s) (∑ i, |(ω i).2.2|) (hsubN π hπPol)
      (Set.subset_biUnion_of_mem (u := fun π' => WbarSetN Γ e π' π0 ω) hπPol)
      (Set.iUnion₂_subset hsubN) (wbar_nonempty.image _) ?_ ?_ (hP3b n ω)
    · intro s w hw
      exact (le_abs_self _).trans (sRegretT_abs_le ω hπ hπ0 w (hw0 w hw) s)
    · intro t w hw V hV
      refine ⟨fun i => if (ω i).2.1 = t then w i else V (ω i).2.1 i, fun i => ?_, fun s => ?_⟩
      · dsimp only; split_ifs
        · exact hw i
        · exact hV _ i
      · by_cases hst : s = t
        · subst hst; simp only [if_true]
          exact sRegretT_congr ω π π0 _ _ s (fun i hi => by simp [hi])
        · simp only [hst, if_false]
          exact sRegretT_congr ω π π0 _ _ s (fun i hi => by simp [hi, hst])
