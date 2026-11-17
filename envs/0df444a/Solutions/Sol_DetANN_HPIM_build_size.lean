-- Prove2me | solution 1 for DetANN.HPIM.build_size
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T19:03:39.280145+00:00
-- url     : https://prove2.me/submissions/1887852e-12f1-4e4a-9275-baeb93ef98fc

import Mathlib
import Definitions.Def_DetANN_HPIMBuild

/-!
# Size of the certified near-neighbour BSP (`DetANN.HPIM.build_size`)

Proof outline (local namespace `DetANN.HPIM.BS`).
* `W w f B`: the sum of a weight `w` over the live build calls of `build f B`. `Starves` at fuel `f`
  forces `W 1 ≥ f` (`starves_le_W`), and `paths.card + 1 = 2·leaves ≤ 2 (1 + 2m W 1)` (`leaves_le`).
* Geometry: fatness of live boxes (`Fat`, `kids_adm`), slabs are OUT (`slab_near_empty`), live boxes are
  not small (`live_not_small`), the root box is fat (`root_fat`).
* Mass: `mass ρ B = Σ_i vol(open B ∩ ball(p_i, √ρ))` is superadditive over the kids (`mass_cut`,
  `kids_sum_le`), at least `λ^m` on a near box with sides `≥ λ` (`mass_ge`), and at most
  `n √((18ρ/m)^m)` (`mass_le`, by the Gaussian bound `volume_ball2_sq_le`).
* Top scale `σ > 16 r` (`top_claim`): `W_top + 2K ≤ 2K μ + 1 + Π`, `K = 2m+2`, with the chain potential
  `Π` (`piPot`), which drops at every node with a unique live kid (`piPot_core`, `piPot_split`).
* Low scales, one dyadic class `(s/2, s]` at a time (`class_claim`): `W_s (s/32)^m ≤ E · mass`, with
  `E` = 1 + number of long sides.
* Assembly: `root_count_bound`, `final_arith`, `build_size_main`.
-/

-- ===== BS_Vol =====
namespace DetANN.HPIM.BS

open MeasureTheory Real Set

variable {m : ℕ}

/-- The open Euclidean ball of squared radius `ρ` around `p`. -/
def ball2 (p : Fin m → ℝ) (ρ : ℝ) : Set (Fin m → ℝ) := {x | ∑ j, (x j - p j) ^ 2 < ρ}

lemma measurableSet_ball2 (p : Fin m → ℝ) (ρ : ℝ) : MeasurableSet (ball2 p ρ) := by
  unfold ball2
  exact measurableSet_lt (by fun_prop) measurable_const

lemma gauss_integral (t : ℝ) (ht : 0 < t) (p : Fin m → ℝ) :
    ∫ x : Fin m → ℝ, ∏ j, Real.exp (-t * (x j - p j) ^ 2) = √(π / t) ^ m := by
  rw [integral_fintype_prod_volume_eq_prod (fun j (y : ℝ) => Real.exp (-t * (y - p j) ^ 2))]
  have : ∀ j : Fin m, ∫ y : ℝ, Real.exp (-t * (y - p j) ^ 2) = √(π / t) := by
    intro j
    rw [integral_sub_right_eq_self (fun y => Real.exp (-t * y ^ 2)) (p j)]
    exact integral_gaussian t
  rw [Finset.prod_congr rfl fun j _ => this j]
  simp

lemma gauss_integrable (t : ℝ) (ht : 0 < t) (p : Fin m → ℝ) :
    Integrable (fun x : Fin m → ℝ => ∏ j, Real.exp (-t * (x j - p j) ^ 2)) := by
  have h := Integrable.fintype_prod_dep (E := fun _ : Fin m => ℝ)
    (f := fun j (y : ℝ) => Real.exp (-t * (y - p j) ^ 2)) (μ := fun _ => volume)
    (fun j => (integrable_exp_neg_mul_sq ht).comp_sub_right (p j))
  simpa [volume_pi] using h

/-- The Gaussian bound with a free parameter `t > 0`. -/
lemma volume_ball2_le_t (p : Fin m → ℝ) (ρ t : ℝ) (ht : 0 < t) :
    volume (ball2 p ρ) ≤ ENNReal.ofReal (Real.exp (t * ρ) * √(π / t) ^ m) := by
  set g : (Fin m → ℝ) → ℝ := fun x => Real.exp (t * ρ) * ∏ j, Real.exp (-t * (x j - p j) ^ 2)
  have hg_int : Integrable g := (gauss_integrable t ht p).const_mul _
  have hg_nn : ∀ x, 0 ≤ g x := fun x => by
    have := Finset.prod_nonneg fun j (_ : j ∈ Finset.univ) =>
      (Real.exp_pos (-t * (x j - p j) ^ 2)).le
    exact mul_nonneg (Real.exp_pos _).le this
  have hint : ∫ x, g x = Real.exp (t * ρ) * √(π / t) ^ m := by
    simp only [g]
    rw [integral_const_mul, gauss_integral t ht p]
  rw [← hint, ofReal_integral_eq_lintegral_ofReal hg_int (Filter.Eventually.of_forall hg_nn)]
  rw [← lintegral_indicator_one (measurableSet_ball2 p ρ)]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ ball2 p ρ
  · rw [indicator_of_mem hx, Pi.one_apply, ENNReal.one_le_ofReal]
    simp only [g]
    rw [← Real.exp_sum, ← Real.exp_add, Real.one_le_exp_iff]
    have : ∑ j, -t * (x j - p j) ^ 2 = -t * ∑ j, (x j - p j) ^ 2 := by
      rw [Finset.mul_sum]
    rw [this]
    have hx' : ∑ j, (x j - p j) ^ 2 < ρ := hx
    nlinarith
  · rw [indicator_of_notMem hx]
    exact bot_le

/-- **Volume of a ball** (`m ≥ 1`, `ρ > 0`): `vol ≤ e^{m/2} (2πρ/m)^{m/2}`. -/
lemma volume_ball2_le (hm : 0 < m) (p : Fin m → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    volume (ball2 p ρ) ≤ ENNReal.ofReal (Real.exp (m / 2) * √(2 * π * ρ / m) ^ m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : 0 < (m : ℝ) / (2 * ρ) := by positivity
  have h := volume_ball2_le_t p ρ _ ht
  have e1 : (m : ℝ) / (2 * ρ) * ρ = m / 2 := by field_simp
  have e2 : π / ((m : ℝ) / (2 * ρ)) = 2 * π * ρ / m := by field_simp
  rwa [e1, e2] at h

lemma volume_ball2_lt_top (p : Fin m → ℝ) (ρ : ℝ) : volume (ball2 p ρ) < ⊤ :=
  lt_of_le_of_lt (volume_ball2_le_t p ρ 1 one_pos) ENNReal.ofReal_lt_top

/-- A convenient numeric form: `vol(ball2 p ρ)^2 ≤ (18 ρ / m)^m`. -/
lemma volume_ball2_sq_le (hm : 0 < m) (p : Fin m → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    (volume (ball2 p ρ)).toReal ^ 2 ≤ (18 * ρ / m) ^ m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := volume_ball2_le hm p ρ hρ
  have hB : 0 ≤ Real.exp (m / 2) * √(2 * π * ρ / m) ^ m := by positivity
  have h1 : (volume (ball2 p ρ)).toReal ≤ Real.exp (m / 2) * √(2 * π * ρ / m) ^ m := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal hB] at this
  have h0 : 0 ≤ (volume (ball2 p ρ)).toReal := ENNReal.toReal_nonneg
  calc (volume (ball2 p ρ)).toReal ^ 2
      ≤ (Real.exp (m / 2) * √(2 * π * ρ / m) ^ m) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (Real.exp 1 * (2 * π * ρ / m)) ^ m := by
        rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt (by positivity), mul_pow,
          ← Real.exp_nat_mul]
        congr 2
        rw [← Real.exp_nat_mul, mul_one]
        congr 1
        push_cast
        ring
    _ ≤ (18 * ρ / m) ^ m := by
        apply pow_le_pow_left₀ (by positivity)
        have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have hπ : π < 3.15 := Real.pi_lt_d2
        have : 0 ≤ ρ / m := by positivity
        have e : Real.exp 1 * (2 * π * ρ / m) = (2 * Real.exp 1 * π) * (ρ / m) := by ring
        have e' : 18 * ρ / m = 18 * (ρ / m) := by ring
        rw [e, e']
        apply mul_le_mul_of_nonneg_right _ this
        nlinarith [Real.exp_pos 1, Real.pi_pos]

end DetANN.HPIM.BS

-- ===== BS_Geo =====
namespace DetANN.HPIM.BS

open DetANN.HPIM

variable {m n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ)

/-- The near set of a box. -/
noncomputable def nearS (lo hi : Fin m → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => boxDist2 lo hi (pts i) ≤ r ^ 2

/-- The good (IN-certificate) set. -/
noncomputable def goodS (lo hi : Fin m → ℝ) : Finset (Fin n) :=
  (nearS pts r lo hi).filter fun i => boxMaxDist2 lo hi (pts i) ≤ (c * r) ^ 2

def IsLive (lo hi : Fin m → ℝ) : Prop :=
  (nearS pts r lo hi).Nonempty ∧ ¬ (goodS pts r c lo hi).Nonempty

/-- Coordinatewise min / max of a point set (0 if empty). -/
noncomputable def aLo (N : Finset (Fin n)) (j : Fin m) : ℝ :=
  if h : N.Nonempty then N.inf' h (fun i => pts i j) else 0

noncomputable def bHi (N : Finset (Fin n)) (j : Fin m) : ℝ :=
  if h : N.Nonempty then N.sup' h (fun i => pts i j) else 0

noncomputable def coreLo (lo hi : Fin m → ℝ) : Fin m → ℝ :=
  fun j => max (aLo pts (nearS pts r lo hi) j - 2 * r) (lo j)

noncomputable def coreHi (lo hi : Fin m → ℝ) : Fin m → ℝ :=
  fun j => min (bHi pts (nearS pts r lo hi) j + 2 * r) (hi j)

/-- Does the live box carve? -/
def Carves (lo hi : Fin m → ℝ) : Prop :=
  2 * sigma (coreLo pts r lo hi) (coreHi pts r lo hi) ≤ sigma lo hi

lemma build_succ_notlive (f : ℕ) (lo hi : Fin m → ℝ) (h : ¬ IsLive pts r c lo hi) :
    ∃ a, build pts r c (f + 1) lo hi = .leaf lo hi a := by
  simp only [build]
  unfold IsLive goodS nearS at h
  split_ifs with h1 h2
  · exact ⟨_, rfl⟩
  · exact absurd ⟨h1, h2⟩ h
  · exact absurd ⟨h1, h2⟩ h
  · exact ⟨_, rfl⟩

lemma build_succ_carve (f : ℕ) (lo hi : Fin m → ℝ) (h : IsLive pts r c lo hi)
    (hc : Carves pts r lo hi) :
    build pts r c (f + 1) lo hi =
      carve (coreLo pts r lo hi) (coreHi pts r lo hi) (build pts r c f) m 0 lo hi := by
  obtain ⟨h1, h2⟩ := h
  unfold Carves coreLo coreHi aLo bHi at hc
  unfold coreLo coreHi aLo bHi
  unfold goodS at h2
  simp only [build]
  unfold nearS at h1 h2 hc ⊢
  rw [dif_pos h1, dif_neg h2]
  simp only [dif_pos h1] at hc ⊢
  rw [if_pos hc]

lemma build_succ_split (f : ℕ) (lo hi : Fin m → ℝ) (h : IsLive pts r c lo hi)
    (hc : ¬ Carves pts r lo hi) (k : Fin m) (hk : longestAxis lo hi = some k) :
    build pts r c (f + 1) lo hi =
      .cut lo hi (build pts r c f lo (setCoord hi k ((lo k + hi k) / 2)))
        (build pts r c f (setCoord lo k ((lo k + hi k) / 2)) hi) := by
  obtain ⟨h1, h2⟩ := h
  unfold Carves coreLo coreHi aLo bHi at hc
  unfold goodS at h2
  simp only [build]
  unfold nearS at h1 h2 hc
  rw [dif_pos h1, dif_neg h2]
  simp only [dif_pos h1] at hc ⊢
  rw [if_neg hc, hk]


/-! ## sigma and the longest axis -/

lemma le_sigma (lo hi : Fin m → ℝ) (j : Fin m) : hi j - lo j ≤ sigma lo hi :=
  le_ciSup (f := fun j => hi j - lo j) (Finite.bddAbove_range _) j

lemma sigma_le (hm : 0 < m) {lo hi : Fin m → ℝ} {x : ℝ} (h : ∀ j, hi j - lo j ≤ x) :
    sigma lo hi ≤ x := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact ciSup_le h

lemma exists_sigma (hm : 0 < m) (lo hi : Fin m → ℝ) : ∃ j, hi j - lo j = sigma lo hi := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact exists_eq_ciSup_of_finite

lemma longestAxis_some (hm : 0 < m) (lo hi : Fin m → ℝ) :
    ∃ k, longestAxis lo hi = some k ∧ hi k - lo k = sigma lo hi := by
  classical
  obtain ⟨j, hj⟩ := exists_sigma hm lo hi
  have hne : (Finset.univ.filter fun j : Fin m => sigma lo hi ≤ hi j - lo j).Nonempty :=
    ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj.ge⟩⟩
  refine ⟨(Finset.univ.filter fun j : Fin m => sigma lo hi ≤ hi j - lo j).min' hne, ?_, ?_⟩
  · unfold longestAxis
    convert dif_pos hne
  · have := (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
    exact le_antisymm (le_sigma _ _ _) this

lemma longestAxis_spec {lo hi : Fin m → ℝ} {k : Fin m} (hk : longestAxis lo hi = some k) :
    hi k - lo k = sigma lo hi := by
  classical
  unfold longestAxis at hk
  split_ifs at hk with hne
  · cases hk
    have := (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
    exact le_antisymm (le_sigma _ _ _) this

/-! ## kids -/

open Classical in
/-- The child boxes of a live box (build calls one level down). -/
noncomputable def kids (lo hi : Fin m → ℝ) : List ((Fin m → ℝ) × (Fin m → ℝ)) :=
  if Carves pts r lo hi then carveBoxes (coreLo pts r lo hi) (coreHi pts r lo hi) m 0 lo hi
  else match longestAxis lo hi with
    | none => []
    | some k => [(lo, setCoord hi k ((lo k + hi k) / 2)), (setCoord lo k ((lo k + hi k) / 2), hi)]

lemma kids_carve {lo hi : Fin m → ℝ} (hc : Carves pts r lo hi) :
    kids pts r lo hi = carveBoxes (coreLo pts r lo hi) (coreHi pts r lo hi) m 0 lo hi := by
  unfold kids; rw [if_pos hc]

lemma kids_split {lo hi : Fin m → ℝ} (hc : ¬ Carves pts r lo hi) {k : Fin m}
    (hk : longestAxis lo hi = some k) :
    kids pts r lo hi =
      [(lo, setCoord hi k ((lo k + hi k) / 2)), (setCoord lo k ((lo k + hi k) / 2), hi)] := by
  unfold kids; rw [if_neg hc, hk]

lemma carveBoxes_length (tlo thi : Fin m → ℝ) :
    ∀ d k lo hi, (carveBoxes tlo thi d k lo hi).length ≤ 2 * d + 1 := by
  intro d
  induction d with
  | zero => intro k lo hi; simp [carveBoxes]
  | succ d ih =>
    intro k lo hi
    simp only [carveBoxes]
    split_ifs <;> (try simp only [List.length_cons, List.length_append, List.length_nil]) <;>
      first
        | omega
        | (have := ih (k + 1) (setCoord lo k (tlo ⟨k, by assumption⟩))
              (setCoord hi k (thi ⟨k, by assumption⟩)); omega)
        | (have := ih (k + 1) (setCoord lo k (tlo ⟨k, by assumption⟩)) hi; omega)
        | (have := ih (k + 1) lo (setCoord hi k (thi ⟨k, by assumption⟩)); omega)
        | (have := ih (k + 1) lo hi; omega)

lemma kids_length (hm : 0 < m) (lo hi : Fin m → ℝ) : (kids pts r lo hi).length ≤ 2 * m + 1 := by
  unfold kids
  split_ifs
  · exact carveBoxes_length _ _ _ _ _ _
  · split <;> simp; omega

/-! ## Starves and leaves through kids -/

lemma starves_succ (hm : 0 < m) {f : ℕ} {lo hi : Fin m → ℝ} (h : Starves pts r c (f + 1) lo hi) :
    IsLive pts r c lo hi ∧ ∃ B ∈ kids pts r lo hi, Starves pts r c f B.1 B.2 := by
  by_cases hl : IsLive pts r c lo hi
  · refine ⟨hl, ?_⟩
    obtain ⟨h1, h2⟩ := hl
    unfold goodS at h2
    by_cases hc : Carves pts r lo hi
    · rw [kids_carve pts r hc]
      have hc' := hc
      unfold Carves coreLo coreHi aLo bHi at hc'
      unfold coreLo coreHi aLo bHi
      simp only [Starves] at h
      unfold nearS at h1 h2 hc' ⊢
      rw [dif_pos h1, if_neg h2] at h
      simp only [dif_pos h1] at hc' h ⊢
      rw [if_pos hc'] at h
      exact h
    · obtain ⟨k, hk, -⟩ := longestAxis_some hm lo hi
      rw [kids_split pts r hc hk]
      have hc' := hc
      unfold Carves coreLo coreHi aLo bHi at hc'
      simp only [Starves] at h
      unfold nearS at h1 h2 hc'
      rw [dif_pos h1, if_neg h2] at h
      simp only [dif_pos h1] at hc' h
      rw [if_neg hc', hk] at h
      rcases h with h | h
      · exact ⟨_, List.mem_cons_self .., h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩
  · exfalso
    unfold IsLive goodS nearS at hl
    simp only [Starves] at h
    split_ifs at h with h1 h2 <;> exact hl ⟨h1, h2⟩

/-- Number of leaves. -/
def leaves : BSP m → ℕ
  | .leaf .. => 1
  | .cut _ _ l t => leaves l + leaves t

lemma paths_card (T : BSP m) : T.paths.card + 1 = 2 * leaves T := by
  induction T with
  | leaf => simp [BSP.paths, leaves]
  | cut lo hi l t ihl iht =>
    simp only [BSP.paths, leaves]
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_union_of_disjoint]
      · rw [Finset.card_image_of_injective _ (List.cons_injective),
          Finset.card_image_of_injective _ (List.cons_injective)]
        omega
      · rw [Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hx'
        simp at hb
    · intro hx
      rcases Finset.mem_union.1 hx with hx | hx <;>
        · obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hx
          simp at ha

lemma carve_leaves (tlo thi : Fin m → ℝ) (bld : (Fin m → ℝ) → (Fin m → ℝ) → BSP m) :
    ∀ d k lo hi, leaves (carve tlo thi bld d k lo hi) =
      ((carveBoxes tlo thi d k lo hi).map fun B => leaves (bld B.1 B.2)).sum := by
  intro d
  induction d with
  | zero => intro k lo hi; simp [carve, carveBoxes]
  | succ d ih =>
    intro k lo hi
    simp only [carve, carveBoxes]
    split_ifs <;> simp [leaves, ih]


/-! ## Weighted counts of live build calls -/

open Classical in
/-- `W w f B`: the sum of `w` over the live build calls (with fuel `≥ 1`) of `build f B`. -/
noncomputable def W (w : (Fin m → ℝ) → (Fin m → ℝ) → ℝ) :
    ℕ → (Fin m → ℝ) → (Fin m → ℝ) → ℝ
  | 0, _, _ => 0
  | f + 1, lo, hi =>
    if IsLive pts r c lo hi then w lo hi + ((kids pts r lo hi).map fun B => W w f B.1 B.2).sum
    else 0

lemma W_zero (w) (lo hi : Fin m → ℝ) : W pts r c w 0 lo hi = 0 := rfl

lemma W_succ_live (w) (f : ℕ) {lo hi : Fin m → ℝ} (h : IsLive pts r c lo hi) :
    W pts r c w (f + 1) lo hi = w lo hi + ((kids pts r lo hi).map fun B => W pts r c w f B.1 B.2).sum := by
  rw [W, if_pos h]

lemma W_notlive (w) (f : ℕ) {lo hi : Fin m → ℝ} (h : ¬ IsLive pts r c lo hi) :
    W pts r c w f lo hi = 0 := by
  cases f with
  | zero => rfl
  | succ f => rw [W, if_neg h]

lemma W_nonneg (w) (hw : ∀ lo hi, 0 ≤ w lo hi) : ∀ f (lo hi : Fin m → ℝ), 0 ≤ W pts r c w f lo hi := by
  intro f
  induction f with
  | zero => intro lo hi; exact le_refl _
  | succ f ih =>
    intro lo hi
    by_cases h : IsLive pts r c lo hi
    · rw [W_succ_live pts r c w f h]
      exact add_nonneg (hw _ _) (List.sum_nonneg fun x hx => by
        obtain ⟨B, -, rfl⟩ := List.mem_map.1 hx; exact ih _ _)
    · rw [W_notlive pts r c w _ h]

lemma starves_le_W (hm : 0 < m) :
    ∀ f (lo hi : Fin m → ℝ), Starves pts r c f lo hi → (f : ℝ) ≤ W pts r c (fun _ _ => 1) f lo hi := by
  intro f
  induction f with
  | zero => intro lo hi _; simp [W_zero]
  | succ f ih =>
    intro lo hi h
    obtain ⟨hl, B, hB, hs⟩ := starves_succ pts r c hm h
    rw [W_succ_live pts r c _ f hl]
    have h1 := ih _ _ hs
    have h2 : W pts r c (fun _ _ => 1) f B.1 B.2 ≤
        ((kids pts r lo hi).map fun B => W pts r c (fun _ _ => 1) f B.1 B.2).sum :=
      List.single_le_sum (fun x hx => by
        obtain ⟨B, -, rfl⟩ := List.mem_map.1 hx
        exact W_nonneg pts r c _ (fun _ _ => zero_le_one) _ _ _) _ (List.mem_map_of_mem hB)
    push_cast
    linarith

lemma leaves_build_succ_live (hm : 0 < m) (f : ℕ) {lo hi : Fin m → ℝ} (h : IsLive pts r c lo hi) :
    leaves (build pts r c (f + 1) lo hi) =
      ((kids pts r lo hi).map fun B => leaves (build pts r c f B.1 B.2)).sum := by
  by_cases hc : Carves pts r lo hi
  · rw [build_succ_carve pts r c f lo hi h hc, kids_carve pts r hc, carve_leaves]
  · obtain ⟨k, hk, -⟩ := longestAxis_some hm lo hi
    rw [build_succ_split pts r c f lo hi h hc k hk, kids_split pts r hc hk]
    simp [leaves]

lemma leaves_le (hm : 0 < m) :
    ∀ f (lo hi : Fin m → ℝ),
      (leaves (build pts r c f lo hi) : ℝ) ≤ 1 + 2 * m * W pts r c (fun _ _ => 1) f lo hi := by
  intro f
  induction f with
  | zero => intro lo hi; simp [build, leaves, W_zero]
  | succ f ih =>
    intro lo hi
    by_cases h : IsLive pts r c lo hi
    · rw [leaves_build_succ_live pts r c hm f h, W_succ_live pts r c _ f h]
      have hlen := kids_length pts r hm lo hi
      set L := kids pts r lo hi
      have key : ∀ L' : List ((Fin m → ℝ) × (Fin m → ℝ)),
          (((L'.map fun B => leaves (build pts r c f B.1 B.2)).sum : ℕ) : ℝ) ≤
            L'.length + 2 * m * (L'.map fun B => W pts r c (fun _ _ => 1) f B.1 B.2).sum := by
        intro L'
        induction L' with
        | nil => simp
        | cons B L' ihL =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
          have := ih B.1 B.2
          linarith
      have hk := key L
      have hlenR : (L.length : ℝ) ≤ 2 * m + 1 := by exact_mod_cast hlen
      nlinarith
    · obtain ⟨a, ha⟩ := build_succ_notlive pts r c f lo hi h
      rw [ha, W_notlive pts r c _ _ h]
      simp [leaves]

end DetANN.HPIM.BS

-- ===== BS_Box =====
namespace DetANN.HPIM.BS

open DetANN.HPIM

variable {m n : ℕ}

/-! ## setCoord -/

lemma setCoord_same (v : Fin m → ℝ) (k : Fin m) (x : ℝ) : setCoord v k x k = x := by
  simp [setCoord]

lemma setCoord_ne (v : Fin m → ℝ) {k : Fin m} {j : Fin m} (h : j ≠ k) (x : ℝ) :
    setCoord v k x j = v j := by
  simp only [setCoord]
  rw [if_neg]
  exact fun h' => h (Fin.ext h')

/-! ## Distances -/

/-- The coordinate term of `boxDist2`. -/
lemma boxDist2_term_nonneg (lo hi p : Fin m → ℝ) (j : Fin m) :
    0 ≤ max (lo j - p j) (max 0 (p j - hi j)) :=
  le_max_of_le_right (le_max_left _ _)

lemma boxDist2_nonneg (lo hi p : Fin m → ℝ) : 0 ≤ boxDist2 lo hi p :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

lemma boxMaxDist2_ge_side (lo hi p : Fin m → ℝ) (j : Fin m) (hj : lo j ≤ hi j) :
    ((hi j - lo j) / 2) ^ 2 ≤ boxMaxDist2 lo hi p := by
  unfold boxMaxDist2
  refine le_trans ?_ (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ j))
  apply pow_le_pow_left₀ (by linarith)
  rcases le_total (p j - lo j) (hi j - p j) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- Monotonicity of `boxDist2` in the box. -/
lemma boxDist2_mono {lo hi lo' hi' : Fin m → ℝ} (hlo : ∀ j, lo j ≤ lo' j) (hhi : ∀ j, hi' j ≤ hi j)
    (p : Fin m → ℝ) : boxDist2 lo hi p ≤ boxDist2 lo' hi' p := by
  unfold boxDist2
  refine Finset.sum_le_sum fun j _ => ?_
  apply pow_le_pow_left₀ (boxDist2_term_nonneg _ _ _ _)
  have := hlo j; have := hhi j
  apply max_le
  · exact le_max_of_le_left (by linarith)
  · apply max_le (boxDist2_term_nonneg _ _ _ _)
    exact le_max_of_le_right (le_max_of_le_right (by linarith))

lemma boxDist2_le_of_mem {lo hi y : Fin m → ℝ} (hy : InBox lo hi y) (p : Fin m → ℝ) :
    boxDist2 lo hi p ≤ ∑ j, (y j - p j) ^ 2 := by
  unfold boxDist2
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← sq_abs (y j - p j)]
  apply pow_le_pow_left₀ (boxDist2_term_nonneg _ _ _ _)
  obtain ⟨h1, h2⟩ := hy j
  apply max_le
  · exact le_trans (by linarith : lo j - p j ≤ y j - p j) (le_abs_self _)
  · exact max_le (abs_nonneg _) (le_trans (by linarith : p j - hi j ≤ -(y j - p j)) (neg_le_abs _))

/-- The clamp of `p` into the box. -/
noncomputable def clamp (lo hi p : Fin m → ℝ) : Fin m → ℝ := fun j => max (lo j) (min (p j) (hi j))

lemma clamp_mem {lo hi : Fin m → ℝ} (h : ∀ j, lo j ≤ hi j) (p : Fin m → ℝ) :
    InBox lo hi (clamp lo hi p) := fun j =>
  ⟨le_max_left _ _, max_le (h j) (min_le_right _ _)⟩

lemma clamp_dist {lo hi : Fin m → ℝ} (h : ∀ j, lo j ≤ hi j) (p : Fin m → ℝ) :
    ∑ j, (clamp lo hi p j - p j) ^ 2 = boxDist2 lo hi p := by
  unfold boxDist2 clamp
  refine Finset.sum_congr rfl fun j _ => ?_
  have := h j
  simp only [max_def, min_def]
  split_ifs <;> first | ring1 | (exfalso; linarith) | (congr 1; linarith) | nlinarith

/-- A near point is within `r` of the box in every coordinate. -/
lemma near_coord {lo hi p : Fin m → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : boxDist2 lo hi p ≤ r ^ 2)
    (j : Fin m) : lo j - r ≤ p j ∧ p j ≤ hi j + r := by
  have ht : (max (lo j - p j) (max 0 (p j - hi j))) ^ 2 ≤ r ^ 2 :=
    le_trans (Finset.single_le_sum (f := fun j => (max (lo j - p j) (max 0 (p j - hi j))) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ j)) h
  have ht' := (pow_le_pow_iff_left₀ (boxDist2_term_nonneg lo hi p j) hr two_ne_zero).1 ht
  have a1 := le_max_left (lo j - p j) (max 0 (p j - hi j))
  have a2 := le_max_right (0 : ℝ) (p j - hi j)
  have a3 := le_max_right (lo j - p j) (max 0 (p j - hi j))
  constructor <;> linarith

/-! ## Near sets, a and b -/

section Pts

variable (pts : Fin n → Fin m → ℝ) (r c : ℝ)

lemma mem_nearS {lo hi : Fin m → ℝ} {i : Fin n} :
    i ∈ nearS pts r lo hi ↔ boxDist2 lo hi (pts i) ≤ r ^ 2 := by
  simp [nearS]

lemma nearS_mono {lo hi lo' hi' : Fin m → ℝ} (hlo : ∀ j, lo j ≤ lo' j) (hhi : ∀ j, hi' j ≤ hi j) :
    nearS pts r lo' hi' ⊆ nearS pts r lo hi := by
  intro i hi'
  rw [mem_nearS] at hi' ⊢
  exact le_trans (boxDist2_mono hlo hhi _) hi'

lemma aLo_le {N : Finset (Fin n)} {i : Fin n} (hi : i ∈ N) (j : Fin m) : aLo pts N j ≤ pts i j := by
  unfold aLo; rw [dif_pos ⟨i, hi⟩]; exact Finset.inf'_le _ hi

lemma le_bHi {N : Finset (Fin n)} {i : Fin n} (hi : i ∈ N) (j : Fin m) : pts i j ≤ bHi pts N j := by
  unfold bHi; rw [dif_pos ⟨i, hi⟩]; exact Finset.le_sup' (fun i => pts i j) hi

lemma aLo_le_bHi {N : Finset (Fin n)} (hN : N.Nonempty) (j : Fin m) : aLo pts N j ≤ bHi pts N j := by
  obtain ⟨i, hi⟩ := hN
  exact (aLo_le pts hi j).trans (le_bHi pts hi j)

lemma aLo_ge {lo hi : Fin m → ℝ} (hr : 0 ≤ r) (hN : (nearS pts r lo hi).Nonempty) (j : Fin m) :
    lo j - r ≤ aLo pts (nearS pts r lo hi) j := by
  unfold aLo; rw [dif_pos hN]
  exact Finset.le_inf' _ _ fun i hi => (near_coord hr ((mem_nearS pts r).1 hi) j).1

lemma bHi_le {lo hi : Fin m → ℝ} (hr : 0 ≤ r) (hN : (nearS pts r lo hi).Nonempty) (j : Fin m) :
    bHi pts (nearS pts r lo hi) j ≤ hi j + r := by
  unfold bHi; rw [dif_pos hN]
  exact Finset.sup'_le _ _ fun i hi => (near_coord hr ((mem_nearS pts r).1 hi) j).2

/-! ## The core -/

variable {pts r}

lemma core_props {lo hi : Fin m → ℝ} (hr : 0 ≤ r) (hN : (nearS pts r lo hi).Nonempty)
    (hle : ∀ j, lo j ≤ hi j) (j : Fin m) :
    lo j ≤ coreLo pts r lo hi j ∧ coreHi pts r lo hi j ≤ hi j ∧
      coreLo pts r lo hi j ≤ coreHi pts r lo hi j ∧ coreLo pts r lo hi j ≤ hi j ∧
      lo j ≤ coreHi pts r lo hi j ∧
      min (hi j - lo j) r ≤ coreHi pts r lo hi j - coreLo pts r lo hi j ∧
      coreHi pts r lo hi j - coreLo pts r lo hi j ≤
        bHi pts (nearS pts r lo hi) j - aLo pts (nearS pts r lo hi) j + 4 * r := by
  have ha := aLo_ge pts r hr hN j
  have hb := bHi_le pts r hr hN j
  have hab := aLo_le_bHi pts hN j
  have h0 := hle j
  unfold coreLo coreHi
  set a := aLo pts (nearS pts r lo hi) j
  set b := bHi pts (nearS pts r lo hi) j
  refine ⟨le_max_right _ _, min_le_right _ _, ?_, ?_, ?_, ?_, ?_⟩
  · exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) h0)
  · exact max_le (by linarith) h0
  · exact le_min (by linarith) h0
  · rcases le_total (b + 2 * r) (hi j) with h1 | h1 <;>
      rcases le_total (a - 2 * r) (lo j) with h2 | h2
    · rw [min_eq_left h1, max_eq_right h2]; exact min_le_of_right_le (by linarith)
    · rw [min_eq_left h1, max_eq_left h2]; exact min_le_of_right_le (by linarith)
    · rw [min_eq_right h1, max_eq_right h2]; exact min_le_left _ _
    · rw [min_eq_right h1, max_eq_left h2]; exact min_le_of_right_le (by linarith)
  · have := min_le_left (b + 2 * r) (hi j)
    have := le_max_left (a - 2 * r) (lo j)
    linarith

/-! ## Lemma 3: live boxes are not small -/

lemma live_not_small {lo hi : Fin m → ℝ} (hle : ∀ j, lo j ≤ hi j) (hr : 0 < r) {ε : ℝ} (hε : 0 ≤ ε)
    (h : IsLive pts r (1 + ε) lo hi) : (ε * r) ^ 2 < ∑ j, (hi j - lo j) ^ 2 := by
  obtain ⟨⟨i, hiN⟩, hg⟩ := h
  by_contra hcon
  push Not at hcon
  apply hg
  refine ⟨i, ?_⟩
  unfold goodS
  rw [Finset.mem_filter]
  refine ⟨hiN, ?_⟩
  have hd := (mem_nearS pts r).1 hiN
  set p := pts i
  set v : Fin m → ℝ := fun j => max (lo j - p j) (max 0 (p j - hi j))
  set l : Fin m → ℝ := fun j => hi j - lo j
  have hv : ∑ j, v j ^ 2 ≤ r ^ 2 := hd
  have hl : ∑ j, l j ^ 2 ≤ (ε * r) ^ 2 := hcon
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v l
  have hvl : ∑ j, v j * l j ≤ ε * r ^ 2 := by
    have h1 : (∑ j, v j * l j) ^ 2 ≤ (ε * r ^ 2) ^ 2 := by
      calc (∑ j, v j * l j) ^ 2 ≤ (∑ j, v j ^ 2) * ∑ j, l j ^ 2 := hcs
        _ ≤ r ^ 2 * (ε * r) ^ 2 := mul_le_mul hv hl (Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (sq_nonneg _)
        _ = (ε * r ^ 2) ^ 2 := by ring
    exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  unfold boxMaxDist2
  calc ∑ j, (max (p j - lo j) (hi j - p j)) ^ 2 ≤ ∑ j, (v j + l j) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h0 := hle j
        apply pow_le_pow_left₀
        · rcases le_total (p j) (lo j) with h | h
          · exact le_max_of_le_right (by linarith)
          · exact le_max_of_le_left (by linarith)
        · apply max_le
          · have := le_max_right (lo j - p j) (max 0 (p j - hi j))
            have := le_max_right (0 : ℝ) (p j - hi j)
            simp only [v, l]; linarith
          · have := le_max_left (lo j - p j) (max 0 (p j - hi j))
            simp only [v, l]; linarith
    _ = ∑ j, v j ^ 2 + 2 * ∑ j, v j * l j + ∑ j, l j ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ r ^ 2 + 2 * (ε * r ^ 2) + (ε * r) ^ 2 := by linarith
    _ = ((1 + ε) * r) ^ 2 := by ring

end Pts

end DetANN.HPIM.BS

-- ===== BS_Carve =====
namespace DetANN.HPIM.BS

open DetANN.HPIM

variable {m : ℕ}

lemma inBox_split {lo hi q : Fin m → ℝ} (k : Fin m) (x : ℝ) (hq : InBox lo hi q) :
    InBox lo (setCoord hi k x) q ∨ InBox (setCoord lo k x) hi q := by
  rcases le_or_gt (q k) x with h | h
  · left
    intro j
    refine ⟨(hq j).1, ?_⟩
    unfold setCoord
    split_ifs with hj
    · have : j = k := Fin.ext hj
      subst this; exact h
    · exact (hq j).2
  · right
    intro j
    refine ⟨?_, (hq j).2⟩
    unfold setCoord
    split_ifs with hj
    · have : j = k := Fin.ext hj
      subst this; exact h.le
    · exact (hq j).1

/-- `setCoord` with a `Fin` index written as a natural number. -/
lemma setCoord_apply (v : Fin m → ℝ) (k : Fin m) (x : ℝ) (j : Fin m) :
    setCoord v k x j = if j = k then x else v j := by
  unfold setCoord
  by_cases h : j = k
  · subst h; simp
  · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h]

section Carve

variable (tlo thi : Fin m → ℝ)

/-- Conditions under which the carve stays inside the box and cuts inside it. -/
def CarveOK (lo hi : Fin m → ℝ) : Prop := ∀ j, tlo j ≤ hi j ∧ lo j ≤ thi j ∧ tlo j ≤ thi j

lemma carveOK_low {lo hi : Fin m → ℝ} (hC : CarveOK tlo thi lo hi) (kk : Fin m) :
    CarveOK tlo thi (setCoord lo kk (tlo kk)) hi := by
  intro j
  refine ⟨(hC j).1, ?_, (hC j).2.2⟩
  rw [setCoord_apply]; split_ifs with h
  · subst h; exact (hC _).2.2
  · exact (hC j).2.1

lemma carveOK_high {lo hi : Fin m → ℝ} (hC : CarveOK tlo thi lo hi) (kk : Fin m) :
    CarveOK tlo thi lo (setCoord hi kk (thi kk)) := by
  intro j
  refine ⟨?_, (hC j).2.1, (hC j).2.2⟩
  rw [setCoord_apply]; split_ifs with h
  · subst h; exact (hC _).2.2
  · exact (hC j).1

lemma carveBoxes_sub :
    ∀ d k (lo hi : Fin m → ℝ), CarveOK tlo thi lo hi → ∀ B ∈ carveBoxes tlo thi d k lo hi,
      (∀ j, lo j ≤ B.1 j) ∧ (∀ j, B.2 j ≤ hi j) := by
  intro d
  induction d with
  | zero =>
    intro k lo hi _ B hB
    simp only [carveBoxes, List.mem_singleton] at hB
    subst hB; exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  | succ d ih =>
    intro k lo hi hC B hB
    simp only [carveBoxes] at hB
    by_cases hk : k < m
    · rw [dif_pos hk] at hB
      set kk : Fin m := ⟨k, hk⟩
      have hrest : ∀ lo' : Fin m → ℝ, (∀ j, lo j ≤ lo' j) → CarveOK tlo thi lo' hi →
          ∀ B ∈ (if hi kk > thi kk then
            carveBoxes tlo thi d (k + 1) lo' (setCoord hi k (thi kk)) ++
              [(setCoord lo' k (thi kk), hi)]
          else carveBoxes tlo thi d (k + 1) lo' hi), (∀ j, lo j ≤ B.1 j) ∧ (∀ j, B.2 j ≤ hi j) := by
        intro lo' hlo' hC' B hB
        by_cases hh : hi kk > thi kk
        · rw [if_pos hh] at hB
          rcases List.mem_append.1 hB with hB | hB
          · obtain ⟨h1, h2⟩ := ih _ _ _ (carveOK_high tlo thi hC' kk) B hB
            refine ⟨fun j => (hlo' j).trans (h1 j), fun j => (h2 j).trans ?_⟩
            show setCoord hi kk (thi kk) j ≤ hi j
            rw [setCoord_apply]; split_ifs with h
            · subst h; exact hh.le
            · exact le_rfl
          · simp only [List.mem_singleton] at hB
            subst hB
            refine ⟨fun j => ?_, fun _ => le_rfl⟩
            show lo j ≤ setCoord lo' kk (thi kk) j
            rw [setCoord_apply]; split_ifs with h
            · subst h; exact (hlo' _).trans (hC' _).2.1
            · exact hlo' j
        · rw [if_neg hh] at hB
          obtain ⟨h1, h2⟩ := ih _ _ _ hC' B hB
          exact ⟨fun j => (hlo' j).trans (h1 j), h2⟩
      by_cases hl : lo kk < tlo kk
      · simp only [hl, ↓reduceIte] at hB
        rcases List.mem_cons.1 hB with hB | hB
        · subst hB
          refine ⟨fun _ => le_rfl, fun j => ?_⟩
          show setCoord hi kk (tlo kk) j ≤ hi j
          rw [setCoord_apply]; split_ifs with h
          · subst h; exact (hC _).1
          · exact le_rfl
        · refine hrest _ (fun j => ?_) (carveOK_low tlo thi hC kk) B hB
          show lo j ≤ setCoord lo kk (tlo kk) j
          rw [setCoord_apply]; split_ifs with h
          · subst h; exact hl.le
          · exact le_rfl
      · simp only [hl, ↓reduceIte] at hB
        exact hrest lo (fun _ => le_rfl) hC B hB
    · rw [dif_neg hk] at hB
      simp only [List.mem_singleton] at hB
      subst hB; exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩

/-- A slab: beyond the core in some coordinate. -/
def Slab (B : (Fin m → ℝ) × (Fin m → ℝ)) : Prop :=
  ∃ j, (B.2 j ≤ tlo j ∧ B.1 j < tlo j) ∨ (thi j ≤ B.1 j ∧ thi j < B.2 j)

/-- The shape of the core box after processing axes `k, …, k + d - 1`. -/
def CoreShape (d k : ℕ) (lo hi : Fin m → ℝ) (B : (Fin m → ℝ) × (Fin m → ℝ)) : Prop :=
  ∀ j : Fin m, (k ≤ j.val ∧ j.val < k + d → B.1 j = tlo j ∧ B.2 j = thi j) ∧
    (¬ (k ≤ j.val ∧ j.val < k + d) → B.1 j = lo j ∧ B.2 j = hi j)

lemma carveBoxes_shape :
    ∀ d k (lo hi : Fin m → ℝ), (∀ j, lo j ≤ tlo j ∧ thi j ≤ hi j) →
      ∀ B ∈ carveBoxes tlo thi d k lo hi, Slab tlo thi B ∨ CoreShape tlo thi d k lo hi B := by
  intro d
  induction d with
  | zero =>
    intro k lo hi _ B hB
    simp only [carveBoxes, List.mem_singleton] at hB
    subst hB
    right; intro j
    exact ⟨fun h => by omega, fun _ => ⟨rfl, rfl⟩⟩
  | succ d ih =>
    intro k lo hi hC B hB
    simp only [carveBoxes] at hB
    by_cases hk : k < m
    · rw [dif_pos hk] at hB
      set kk : Fin m := ⟨k, hk⟩
      have hrest : ∀ lo' : Fin m → ℝ, lo' kk = tlo kk → (∀ j, j ≠ kk → lo' j = lo j) →
          ∀ B ∈ (if hi kk > thi kk then
            carveBoxes tlo thi d (k + 1) lo' (setCoord hi k (thi kk)) ++
              [(setCoord lo' k (thi kk), hi)]
          else carveBoxes tlo thi d (k + 1) lo' hi),
            Slab tlo thi B ∨ CoreShape tlo thi (d + 1) k lo hi B := by
        intro lo' hk' hj' B hB
        have hrec : ∀ hi' : Fin m → ℝ, hi' kk = thi kk → (∀ j, j ≠ kk → hi' j = hi j) →
            ∀ B ∈ carveBoxes tlo thi d (k + 1) lo' hi',
              Slab tlo thi B ∨ CoreShape tlo thi (d + 1) k lo hi B := by
          intro hi' hk'' hj'' B hB
          have hC' : ∀ j, lo' j ≤ tlo j ∧ thi j ≤ hi' j := by
            intro j
            by_cases h : j = kk
            · subst h; exact ⟨hk'.le, hk''.ge⟩
            · rw [hj' j h, hj'' j h]; exact hC j
          rcases ih (k + 1) lo' hi' hC' B hB with h | h
          · exact Or.inl h
          · right; intro j
            obtain ⟨h1, h2⟩ := h j
            by_cases hjk : j = kk
            · subst hjk
              have := h2 (by simp [kk])
              rw [hk', hk''] at this
              exact ⟨fun _ => this, fun h => absurd ⟨le_rfl, by simp [kk]⟩ h⟩
            · have hjk' : j.val ≠ k := fun h => hjk (Fin.ext h)
              refine ⟨fun hr => h1 (by omega), fun hr => ?_⟩
              have := h2 (by omega)
              rw [hj' j hjk, hj'' j hjk] at this
              exact this
        by_cases hh : hi kk > thi kk
        · rw [if_pos hh] at hB
          rcases List.mem_append.1 hB with hB | hB
          · exact hrec _ (setCoord_same _ _ _) (fun j h => setCoord_ne _ h _) B hB
          · simp only [List.mem_singleton] at hB
            subst hB
            left
            refine ⟨kk, Or.inr ⟨?_, hh⟩⟩
            show thi kk ≤ setCoord lo' kk (thi kk) kk
            rw [setCoord_same]
        · rw [if_neg hh] at hB
          exact hrec hi (le_antisymm (not_lt.1 hh) (hC kk).2) (fun _ _ => rfl) B hB
      by_cases hl : lo kk < tlo kk
      · simp only [hl, ↓reduceIte] at hB
        rcases List.mem_cons.1 hB with hB | hB
        · subst hB
          left
          refine ⟨kk, Or.inl ⟨?_, hl⟩⟩
          show setCoord hi kk (tlo kk) kk ≤ tlo kk
          rw [setCoord_same]
        · exact hrest _ (setCoord_same _ _ _) (fun j h => setCoord_ne _ h _) B hB
      · simp only [hl, ↓reduceIte] at hB
        exact hrest lo (le_antisymm (hC kk).1 (not_lt.1 hl)) (fun _ _ => rfl) B hB
    · rw [dif_neg hk] at hB
      simp only [List.mem_singleton] at hB
      subst hB
      right; intro j
      exact ⟨fun h => absurd (lt_of_le_of_lt h.1 j.isLt) hk, fun _ => ⟨rfl, rfl⟩⟩

lemma carveBoxes_slab_or_core {lo hi : Fin m → ℝ} (hC : ∀ j, lo j ≤ tlo j ∧ thi j ≤ hi j)
    {B : (Fin m → ℝ) × (Fin m → ℝ)} (hB : B ∈ carveBoxes tlo thi m 0 lo hi) :
    Slab tlo thi B ∨ B = (tlo, thi) := by
  rcases carveBoxes_shape tlo thi m 0 lo hi hC B hB with h | h
  · exact Or.inl h
  · right
    obtain ⟨B1, B2⟩ := B
    simp only [Prod.mk.injEq]
    constructor <;> funext j
    · exact ((h j).1 ⟨Nat.zero_le _, by simp⟩).1
    · exact ((h j).1 ⟨Nat.zero_le _, by simp⟩).2

lemma carveBoxes_cover :
    ∀ d k (lo hi y : Fin m → ℝ), InBox lo hi y →
      ∃ B ∈ carveBoxes tlo thi d k lo hi, InBox B.1 B.2 y := by
  intro d
  induction d with
  | zero => intro k lo hi y hy; exact ⟨_, List.mem_singleton_self _, hy⟩
  | succ d ih =>
    intro k lo hi y hy
    simp only [carveBoxes]
    by_cases hk : k < m
    · rw [dif_pos hk]
      set kk : Fin m := ⟨k, hk⟩
      have hrest : ∀ lo' : Fin m → ℝ, InBox lo' hi y →
          ∃ B ∈ (if hi kk > thi kk then
            carveBoxes tlo thi d (k + 1) lo' (setCoord hi k (thi kk)) ++
              [(setCoord lo' k (thi kk), hi)]
          else carveBoxes tlo thi d (k + 1) lo' hi), InBox B.1 B.2 y := by
        intro lo' hy'
        by_cases hh : hi kk > thi kk
        · rw [if_pos hh]
          rcases inBox_split kk (thi kk) hy' with h | h
          · obtain ⟨B, hB, hyB⟩ := ih (k + 1) lo' _ y h
            exact ⟨B, List.mem_append_left _ hB, hyB⟩
          · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h⟩
        · rw [if_neg hh]
          exact ih (k + 1) lo' hi y hy'
      by_cases hl : lo kk < tlo kk
      · simp only [hl, ↓reduceIte]
        rcases inBox_split kk (tlo kk) hy with h | h
        · exact ⟨_, List.mem_cons_self .., h⟩
        · obtain ⟨B, hB, hyB⟩ := hrest _ h
          exact ⟨B, List.mem_cons_of_mem _ hB, hyB⟩
      · simp only [hl, ↓reduceIte]
        exact hrest lo hy
    · rw [dif_neg hk]
      exact ⟨_, List.mem_singleton_self _, hy⟩

/-- Superadditivity of a cut-additive mass over the carve. -/
lemma carveBoxes_sum_le (g : (Fin m → ℝ) → (Fin m → ℝ) → ℝ)
    (hcut : ∀ (lo hi : Fin m → ℝ) (k : Fin m) (t : ℝ), lo k ≤ t → t ≤ hi k →
      g lo (setCoord hi k t) + g (setCoord lo k t) hi ≤ g lo hi) :
    ∀ d k (lo hi : Fin m → ℝ), CarveOK tlo thi lo hi →
      ((carveBoxes tlo thi d k lo hi).map fun B => g B.1 B.2).sum ≤ g lo hi := by
  intro d
  induction d with
  | zero => intro k lo hi _; simp [carveBoxes]
  | succ d ih =>
    intro k lo hi hC
    simp only [carveBoxes]
    by_cases hk : k < m
    · rw [dif_pos hk]
      set kk : Fin m := ⟨k, hk⟩
      have hrest : ∀ lo' : Fin m → ℝ, CarveOK tlo thi lo' hi →
          ((if hi kk > thi kk then
            carveBoxes tlo thi d (k + 1) lo' (setCoord hi k (thi kk)) ++
              [(setCoord lo' k (thi kk), hi)]
          else carveBoxes tlo thi d (k + 1) lo' hi).map fun B => g B.1 B.2).sum ≤ g lo' hi := by
        intro lo' hC'
        by_cases hh : hi kk > thi kk
        · rw [if_pos hh, List.map_append, List.sum_append]
          have h1 := ih (k + 1) lo' _ (carveOK_high tlo thi hC' kk)
          have h2 := hcut lo' hi kk (thi kk) (hC' kk).2.1 hh.le
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          linarith
        · rw [if_neg hh]
          exact ih (k + 1) lo' hi hC'
      by_cases hl : lo kk < tlo kk
      · simp only [hl, ↓reduceIte, List.map_cons, List.sum_cons]
        have h1 := hrest _ (carveOK_low tlo thi hC kk)
        have h2 := hcut lo hi kk (tlo kk) hl.le (hC kk).1
        linarith
      · simp only [hl, ↓reduceIte]
        exact hrest lo hC
    · rw [dif_neg hk]
      simp

end Carve

end DetANN.HPIM.BS

-- ===== BS_Kids =====
namespace DetANN.HPIM.BS

open DetANN.HPIM

variable {m n : ℕ} {pts : Fin n → Fin m → ℝ} {r c : ℝ}

/-- Fatness (Lemma 1). -/
def Fat (r : ℝ) (lo hi : Fin m → ℝ) : Prop :=
  (∀ j, lo j ≤ hi j) ∧ ∀ j, min (sigma lo hi / 2) r ≤ hi j - lo j

/-- Admissible: fat if live. -/
def Adm (pts : Fin n → Fin m → ℝ) (r c : ℝ) (lo hi : Fin m → ℝ) : Prop :=
  IsLive pts r c lo hi → Fat r lo hi

lemma term_ge_left (lo hi p : Fin m → ℝ) (j : Fin m) :
    lo j - p j ≤ max (lo j - p j) (max 0 (p j - hi j)) := le_max_left _ _

lemma term_ge_right (lo hi p : Fin m → ℝ) (j : Fin m) :
    p j - hi j ≤ max (lo j - p j) (max 0 (p j - hi j)) :=
  le_max_of_le_right (le_max_right _ _)

lemma boxDist2_ge_term (lo hi p : Fin m → ℝ) (j : Fin m) :
    (max (lo j - p j) (max 0 (p j - hi j))) ^ 2 ≤ boxDist2 lo hi p :=
  Finset.single_le_sum (f := fun j => (max (lo j - p j) (max 0 (p j - hi j))) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ j)

lemma sigma_mono (hm : 0 < m) {lo hi lo' hi' : Fin m → ℝ} (hlo : ∀ j, lo j ≤ lo' j)
    (hhi : ∀ j, hi' j ≤ hi j) : sigma lo' hi' ≤ sigma lo hi :=
  sigma_le hm fun j => by have := le_sigma lo hi j; linarith [hlo j, hhi j]

lemma sigma_nonneg (hm : 0 < m) {lo hi : Fin m → ℝ} (h : ∀ j, lo j ≤ hi j) : 0 ≤ sigma lo hi := by
  have := le_sigma lo hi ⟨0, hm⟩
  linarith [h ⟨0, hm⟩]

/-- The core satisfies the carve conditions. -/
lemma core_carveOK (hr : 0 < r) {lo hi : Fin m → ℝ} (hN : (nearS pts r lo hi).Nonempty)
    (hle : ∀ j, lo j ≤ hi j) :
    CarveOK (coreLo pts r lo hi) (coreHi pts r lo hi) lo hi ∧
      ∀ j, lo j ≤ coreLo pts r lo hi j ∧ coreHi pts r lo hi j ≤ hi j := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · obtain ⟨-, -, h3, h4, h5, -⟩ := core_props hr.le hN hle j
    exact ⟨h4, h5, h3⟩
  · obtain ⟨h1, h2, -⟩ := core_props hr.le hN hle j
    exact ⟨h1, h2⟩

/-- Slabs have no near point. -/
lemma slab_near_empty (hr : 0 < r) {lo hi : Fin m → ℝ} (hN : (nearS pts r lo hi).Nonempty)
    (hle : ∀ j, lo j ≤ hi j) {B : (Fin m → ℝ) × (Fin m → ℝ)}
    (hs : Slab (coreLo pts r lo hi) (coreHi pts r lo hi) B)
    (hsub : (∀ j, lo j ≤ B.1 j) ∧ (∀ j, B.2 j ≤ hi j)) : nearS pts r B.1 B.2 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hiS
  by_cases hiB : i ∈ nearS pts r lo hi
  · obtain ⟨j, hj⟩ := hs
    have hd := (mem_nearS pts r).1 hiS
    have h4r : (2 * r) ^ 2 ≤ boxDist2 B.1 B.2 (pts i) := by
      refine le_trans ?_ (boxDist2_ge_term _ _ _ j)
      apply pow_le_pow_left₀ (by linarith)
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- low slab: the core starts at `a - 2r`
        have hlt : lo j < coreLo pts r lo hi j := lt_of_le_of_lt (hsub.1 j) h2
        have hc : coreLo pts r lo hi j = aLo pts (nearS pts r lo hi) j - 2 * r := by
          unfold coreLo at hlt ⊢
          rcases le_total (aLo pts (nearS pts r lo hi) j - 2 * r) (lo j) with h | h
          · rw [max_eq_right h] at hlt; exact absurd hlt (lt_irrefl _)
          · exact max_eq_left h
        have ha := aLo_le pts hiB j
        exact le_trans (by linarith) (term_ge_right _ _ _ j)
      · have hlt : coreHi pts r lo hi j < hi j := lt_of_lt_of_le h2 (hsub.2 j)
        have hc : coreHi pts r lo hi j = bHi pts (nearS pts r lo hi) j + 2 * r := by
          unfold coreHi at hlt ⊢
          rcases le_total (bHi pts (nearS pts r lo hi) j + 2 * r) (hi j) with h | h
          · exact min_eq_left h
          · rw [min_eq_right h] at hlt; exact absurd hlt (lt_irrefl _)
        have hb := le_bHi pts hiB j
        exact le_trans (by linarith) (term_ge_left _ _ _ j)
    nlinarith
  · exact hiB (nearS_mono pts r hsub.1 hsub.2 hiS)

/-- The split halves of a box. -/
lemma split_props {lo hi : Fin m → ℝ} (hle : ∀ j, lo j ≤ hi j) (k : Fin m) :
    let mid := (lo k + hi k) / 2
    (∀ j, lo j ≤ setCoord hi k mid j) ∧ (∀ j, setCoord hi k mid j ≤ hi j) ∧
      (∀ j, lo j ≤ setCoord lo k mid j) ∧ (∀ j, setCoord lo k mid j ≤ hi j) := by
  intro mid
  have h := hle k
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩ <;>
    (rw [setCoord_apply]; split_ifs with hj
     · subst hj; simp only [mid]; linarith
     · first | exact hle j | exact le_rfl)


lemma setCoord_side_k (lo hi : Fin m → ℝ) (k : Fin m) :
    setCoord hi k ((lo k + hi k) / 2) k - lo k = (hi k - lo k) / 2 ∧
      hi k - setCoord lo k ((lo k + hi k) / 2) k = (hi k - lo k) / 2 := by
  rw [setCoord_same, setCoord_same]; constructor <;> ring

lemma split_kids_fat (hm : 0 < m) {lo hi : Fin m → ℝ} (hF : Fat r lo hi) {k : Fin m}
    (hk : hi k - lo k = sigma lo hi) :
    Fat r lo (setCoord hi k ((lo k + hi k) / 2)) ∧ Fat r (setCoord lo k ((lo k + hi k) / 2)) hi := by
  obtain ⟨h1, h2, h3, h4⟩ := split_props hF.1 k
  have hs1 := sigma_mono hm (lo := lo) (lo' := lo) (fun _ => le_rfl) h2
  have hs2 := sigma_mono hm (hi := hi) (hi' := hi) h3 (fun _ => le_rfl)
  obtain ⟨e1, e2⟩ := setCoord_side_k lo hi k
  refine ⟨⟨h1, fun j => ?_⟩, ⟨h4, fun j => ?_⟩⟩
  · by_cases hj : j = k
    · subst hj; rw [e1, hk]
      exact min_le_of_left_le (by linarith)
    · rw [setCoord_ne _ hj]
      exact le_trans (min_le_min_right _ (by linarith)) (hF.2 j)
  · by_cases hj : j = k
    · subst hj; rw [e2, hk]
      exact min_le_of_left_le (by linarith)
    · rw [setCoord_ne _ hj]
      exact le_trans (min_le_min_right _ (by linarith)) (hF.2 j)

lemma core_fat (hm : 0 < m) (hr : 0 < r) {lo hi : Fin m → ℝ} (hN : (nearS pts r lo hi).Nonempty)
    (hF : Fat r lo hi) : Fat r (coreLo pts r lo hi) (coreHi pts r lo hi) := by
  have hC := (core_carveOK hr hN hF.1).2
  have hs := sigma_mono hm (fun j => (hC j).1) (fun j => (hC j).2)
  refine ⟨fun j => (core_props hr.le hN hF.1 j).2.2.1, fun j => ?_⟩
  have h6 := (core_props hr.le hN hF.1 j).2.2.2.2.2.1
  refine le_trans ?_ h6
  rcases le_total (hi j - lo j) r with h | h
  · rw [min_eq_left h]
    exact le_trans (min_le_min_right _ (by linarith)) (hF.2 j)
  · rw [min_eq_right h]; exact min_le_right _ _

variable (pts r c)

/-- The two shapes of the kids of a live fat box. -/
lemma kids_cases (hm : 0 < m) (hr : 0 < r) {lo hi : Fin m → ℝ} (hl : IsLive pts r c lo hi)
    (hF : Fat r lo hi) :
    (Carves pts r lo hi ∧ ∀ B ∈ kids pts r lo hi,
        ((∀ j, lo j ≤ B.1 j) ∧ (∀ j, B.2 j ≤ hi j)) ∧
        (nearS pts r B.1 B.2 = ∅ ∨ B = (coreLo pts r lo hi, coreHi pts r lo hi))) ∨
    (¬ Carves pts r lo hi ∧ ∃ k, longestAxis lo hi = some k ∧ hi k - lo k = sigma lo hi ∧
      kids pts r lo hi = [(lo, setCoord hi k ((lo k + hi k) / 2)),
        (setCoord lo k ((lo k + hi k) / 2), hi)]) := by
  by_cases hc : Carves pts r lo hi
  · left
    refine ⟨hc, fun B hB => ?_⟩
    rw [kids_carve pts r hc] at hB
    obtain ⟨hOK, hC0⟩ := core_carveOK hr hl.1 hF.1
    have hsub := carveBoxes_sub _ _ m 0 lo hi hOK B hB
    refine ⟨hsub, ?_⟩
    rcases carveBoxes_slab_or_core _ _ hC0 hB with h | h
    · exact Or.inl (slab_near_empty hr hl.1 hF.1 h hsub)
    · exact Or.inr h
  · right
    obtain ⟨k, hk, hk'⟩ := longestAxis_some hm lo hi
    exact ⟨hc, k, hk, hk', kids_split pts r hc hk⟩

lemma kids_sub (hm : 0 < m) (hr : 0 < r) {lo hi : Fin m → ℝ} (hl : IsLive pts r c lo hi)
    (hF : Fat r lo hi) : ∀ B ∈ kids pts r lo hi, (∀ j, lo j ≤ B.1 j) ∧ (∀ j, B.2 j ≤ hi j) := by
  rcases kids_cases pts r c hm hr hl hF with ⟨-, h⟩ | ⟨-, k, -, -, h⟩
  · exact fun B hB => (h B hB).1
  · rw [h]
    obtain ⟨h1, h2, h3, h4⟩ := split_props hF.1 k
    intro B hB
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    · exact ⟨fun _ => le_rfl, h2⟩
    · exact ⟨h3, fun _ => le_rfl⟩

lemma kids_sigma_le (hm : 0 < m) (hr : 0 < r) {lo hi : Fin m → ℝ} (hl : IsLive pts r c lo hi)
    (hF : Fat r lo hi) : ∀ B ∈ kids pts r lo hi, sigma B.1 B.2 ≤ sigma lo hi := fun B hB =>
  sigma_mono hm (kids_sub pts r c hm hr hl hF B hB).1 (kids_sub pts r c hm hr hl hF B hB).2

lemma notLive_of_near_empty {lo hi : Fin m → ℝ} (h : nearS pts r lo hi = ∅) :
    ¬ IsLive pts r c lo hi := fun hl => by
  have := hl.1; rw [h] at this; exact Finset.not_nonempty_empty this

lemma kids_adm (hm : 0 < m) (hr : 0 < r) {lo hi : Fin m → ℝ} (hl : IsLive pts r c lo hi)
    (hF : Fat r lo hi) : ∀ B ∈ kids pts r lo hi, Adm pts r c B.1 B.2 := by
  rcases kids_cases pts r c hm hr hl hF with ⟨-, h⟩ | ⟨-, k, -, hk', h⟩
  · intro B hB hlB
    rcases (h B hB).2 with h' | h'
    · exact absurd hlB (notLive_of_near_empty pts r c h')
    · rw [h']; exact core_fat hm hr hl.1 hF
  · rw [h]
    obtain ⟨f1, f2⟩ := split_kids_fat hm hF hk'
    intro B hB _
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    · exact f1
    · exact f2

lemma kids_cover (hm : 0 < m) {lo hi y : Fin m → ℝ} (hy : InBox lo hi y) :
    ∃ B ∈ kids pts r lo hi, InBox B.1 B.2 y := by
  by_cases hc : Carves pts r lo hi
  · rw [kids_carve pts r hc]
    exact carveBoxes_cover _ _ _ _ _ _ _ hy
  · obtain ⟨k, hk, -⟩ := longestAxis_some hm lo hi
    rw [kids_split pts r hc hk]
    rcases inBox_split k ((lo k + hi k) / 2) hy with h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩

/-- Every near point of the box is near some kid. -/
lemma near_kids (hm : 0 < m) {lo hi : Fin m → ℝ} (hle : ∀ j, lo j ≤ hi j) {i : Fin n}
    (hiN : i ∈ nearS pts r lo hi) : ∃ B ∈ kids pts r lo hi, i ∈ nearS pts r B.1 B.2 := by
  obtain ⟨B, hB, hyB⟩ := kids_cover pts r hm (clamp_mem hle (pts i))
  refine ⟨B, hB, (mem_nearS pts r).2 ?_⟩
  have := boxDist2_le_of_mem hyB (pts i)
  rw [clamp_dist hle] at this
  exact this.trans ((mem_nearS pts r).1 hiN)

/-- Superadditivity of a cut-additive mass over the kids. -/
lemma kids_sum_le (hm : 0 < m) (hr : 0 < r) {lo hi : Fin m → ℝ} (hl : IsLive pts r c lo hi)
    (hF : Fat r lo hi) (g : (Fin m → ℝ) → (Fin m → ℝ) → ℝ)
    (hcut : ∀ (lo hi : Fin m → ℝ) (k : Fin m) (t : ℝ), lo k ≤ t → t ≤ hi k →
      g lo (setCoord hi k t) + g (setCoord lo k t) hi ≤ g lo hi) :
    ((kids pts r lo hi).map fun B => g B.1 B.2).sum ≤ g lo hi := by
  by_cases hc : Carves pts r lo hi
  · rw [kids_carve pts r hc]
    exact carveBoxes_sum_le _ _ g hcut _ _ _ _ (core_carveOK hr hl.1 hF.1).1
  · obtain ⟨k, hk, -⟩ := longestAxis_some hm lo hi
    rw [kids_split pts r hc hk]
    have := hF.1 k
    simpa using hcut lo hi k ((lo k + hi k) / 2) (by linarith) (by linarith)

end DetANN.HPIM.BS

-- ===== BS_Mass =====
namespace DetANN.HPIM.BS

open DetANN.HPIM MeasureTheory Set

variable {m n : ℕ}

/-- The open box. -/
def openBox (lo hi : Fin m → ℝ) : Set (Fin m → ℝ) := Set.pi Set.univ fun j => Ioo (lo j) (hi j)

lemma measurableSet_openBox (lo hi : Fin m → ℝ) : MeasurableSet (openBox lo hi) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- The mass of a box: total volume of the open box within squared distance `ρ` of the points. -/
noncomputable def mass (pts : Fin n → Fin m → ℝ) (ρ : ℝ) (lo hi : Fin m → ℝ) : ℝ :=
  ∑ i, (volume (openBox lo hi ∩ ball2 (pts i) ρ)).toReal

lemma mass_nonneg (pts : Fin n → Fin m → ℝ) (ρ : ℝ) (lo hi : Fin m → ℝ) : 0 ≤ mass pts ρ lo hi :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

lemma vol_inter_ne_top (lo hi p : Fin m → ℝ) (ρ : ℝ) : volume (openBox lo hi ∩ ball2 p ρ) ≠ ⊤ :=
  ne_top_of_le_ne_top (volume_ball2_lt_top p ρ).ne (measure_mono inter_subset_right)

/-- Cut additivity. -/
lemma mass_cut (pts : Fin n → Fin m → ℝ) (ρ : ℝ) (lo hi : Fin m → ℝ) (k : Fin m) (t : ℝ)
    (h1 : lo k ≤ t) (h2 : t ≤ hi k) :
    mass pts ρ lo (setCoord hi k t) + mass pts ρ (setCoord lo k t) hi ≤ mass pts ρ lo hi := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  set S := ball2 (pts i) ρ
  set A := openBox lo (setCoord hi k t) ∩ S
  set B := openBox (setCoord lo k t) hi ∩ S
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have ha := (hxA.1 k (mem_univ _)).2
    have hb := (hxB.1 k (mem_univ _)).1
    rw [setCoord_same] at ha hb
    linarith
  have hB : MeasurableSet B := (measurableSet_openBox _ _).inter (measurableSet_ball2 _ _)
  have hsub : A ∪ B ⊆ openBox lo hi ∩ S := by
    rintro x (⟨hx, hxS⟩ | ⟨hx, hxS⟩)
    · refine ⟨fun j _ => ?_, hxS⟩
      have := hx j (mem_univ _)
      simp only [mem_Ioo] at this ⊢
      rw [setCoord_apply] at this
      split_ifs at this with hj
      · subst hj; exact ⟨this.1, this.2.trans_le h2⟩
      · exact this
    · refine ⟨fun j _ => ?_, hxS⟩
      have := hx j (mem_univ _)
      simp only [mem_Ioo] at this ⊢
      rw [setCoord_apply] at this
      split_ifs at this with hj
      · subst hj; exact ⟨h1.trans_lt this.1, this.2⟩
      · exact this
  rw [← ENNReal.toReal_add (vol_inter_ne_top _ _ _ _) (vol_inter_ne_top _ _ _ _),
    ← measure_union hdisj hB]
  exact ENNReal.toReal_mono (vol_inter_ne_top _ _ _ _) (measure_mono hsub)

/-- Upper bound for the mass. -/
lemma mass_le (hm : 0 < m) (pts : Fin n → Fin m → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (lo hi : Fin m → ℝ) :
    mass pts ρ lo hi ≤ n * Real.sqrt ((18 * ρ / m) ^ m) := by
  unfold mass
  have : ∀ i, (volume (openBox lo hi ∩ ball2 (pts i) ρ)).toReal ≤ Real.sqrt ((18 * ρ / m) ^ m) := by
    intro i
    have h1 := ENNReal.toReal_mono (volume_ball2_lt_top (pts i) ρ).ne
      (measure_mono (μ := volume) (inter_subset_right (s := openBox lo hi) (t := ball2 (pts i) ρ)))
    have h2 := volume_ball2_sq_le hm (pts i) ρ hρ
    exact h1.trans (Real.le_sqrt_of_sq_le h2)
  calc ∑ i, (volume (openBox lo hi ∩ ball2 (pts i) ρ)).toReal
      ≤ ∑ _i : Fin n, Real.sqrt ((18 * ρ / m) ^ m) := Finset.sum_le_sum fun i _ => this i
    _ = n * Real.sqrt ((18 * ρ / m) ^ m) := by simp

/-- Lower bound for the mass of a box with all sides `≥ λ` and a point within `r`. -/
lemma mass_ge (hm : 0 < m) (pts : Fin n → Fin m → ℝ) {r lam : ℝ} (hlam : 0 < lam)
    {lo hi : Fin m → ℝ} (hside : ∀ j, lam ≤ hi j - lo j) {i : Fin n}
    (hiD : boxDist2 lo hi (pts i) ≤ r ^ 2) :
    lam ^ m ≤ mass pts (2 * r ^ 2 + 2 * m * lam ^ 2) lo hi := by
  have hle : ∀ j, lo j ≤ hi j := fun j => by linarith [hside j]
  set y := clamp lo hi (pts i)
  have hy := clamp_mem hle (pts i)
  have hyd := clamp_dist hle (pts i)
  set cl : Fin m → ℝ := fun j => min (y j) (hi j - lam)
  set cu : Fin m → ℝ := fun j => cl j + lam
  have hcube : openBox cl cu ⊆ openBox lo hi ∩ ball2 (pts i) (2 * r ^ 2 + 2 * m * lam ^ 2) := by
    intro x hx
    have hx' : ∀ j, cl j < x j ∧ x j < cl j + lam := fun j => hx j (mem_univ _)
    have hcl : ∀ j, lo j ≤ cl j := fun j =>
      le_min (hy j).1 (by linarith [hside j])
    have hxy : ∀ j, (x j - y j) ^ 2 < lam ^ 2 := by
      intro j
      have h1 := (hx' j).1; have h2 := (hx' j).2
      have h3 : cl j ≤ y j := min_le_left _ _
      have h4 : y j ≤ cl j + lam := by
        simp only [cl]
        rcases le_total (y j) (hi j - lam) with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]; linarith [(hy j).2]
      have : |x j - y j| < lam := abs_lt.2 ⟨by linarith, by linarith⟩
      calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
        _ < lam ^ 2 := by
          apply pow_lt_pow_left₀ this (abs_nonneg _) two_ne_zero
    refine ⟨fun j _ => ⟨(hcl j).trans_lt (hx' j).1, ?_⟩, ?_⟩
    · have : cl j ≤ hi j - lam := min_le_right _ _
      linarith [(hx' j).2]
    · show ∑ j, (x j - pts i j) ^ 2 < 2 * r ^ 2 + 2 * m * lam ^ 2
      have hs1 : ∑ j, (x j - y j) ^ 2 < ∑ _j : Fin m, lam ^ 2 :=
        Finset.sum_lt_sum_of_nonempty ⟨⟨0, hm⟩, Finset.mem_univ _⟩ fun j _ => hxy j
      have hs2 : ∑ j, (x j - pts i j) ^ 2 ≤ ∑ j, (2 * (x j - y j) ^ 2 + 2 * (y j - pts i j) ^ 2) :=
        Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg (x j - y j - (y j - pts i j))]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hyd] at hs2
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs1
      nlinarith
  have hvol : (volume (openBox cl cu)).toReal = lam ^ m := by
    unfold openBox
    rw [Real.volume_pi_Ioo_toReal (fun j => by simp only [cu]; linarith)]
    simp [cu]
  calc lam ^ m = (volume (openBox cl cu)).toReal := hvol.symm
    _ ≤ (volume (openBox lo hi ∩ ball2 (pts i) (2 * r ^ 2 + 2 * m * lam ^ 2))).toReal :=
        ENNReal.toReal_mono (vol_inter_ne_top _ _ _ _) (measure_mono hcube)
    _ ≤ mass pts (2 * r ^ 2 + 2 * m * lam ^ 2) lo hi :=
        Finset.single_le_sum (f := fun i => (volume (openBox lo hi ∩
          ball2 (pts i) (2 * r ^ 2 + 2 * m * lam ^ 2))).toReal)
          (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)

end DetANN.HPIM.BS

-- ===== BS_Pot =====
namespace DetANN.HPIM.BS

open DetANN.HPIM

variable {m n : ℕ}

/-! ## List helpers -/

lemma list_sum_map_filter {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] (f : α → ℝ)
    (h : ∀ x ∈ l, ¬ P x → f x = 0) : (l.map f).sum = ((l.filter P).map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases ha : P a
    · simp [ha, ih']
    · simp [ha, ih', h a List.mem_cons_self ha]

lemma list_sum_filter_le {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] (f : α → ℝ)
    (h : ∀ x ∈ l, 0 ≤ f x) : ((l.filter P).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha0 := h a List.mem_cons_self
    by_cases ha : P a
    · simp [ha]; linarith
    · simp [ha]; linarith

lemma list_sum_le_mul_length {α : Type*} (l : List α) (f g : α → ℝ) (K : ℝ)
    (h : ∀ x ∈ l, f x ≤ K * g x - K) : (l.map f).sum ≤ K * (l.map g).sum - K * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

lemma list_sum_finset_swap {α : Type*} (l : List α) (s : Finset ℕ) (F : ℕ → α → ℝ) :
    (l.map fun x => ∑ k ∈ s, F k x).sum = ∑ k ∈ s, (l.map (F k)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

section W

variable (pts : Fin n → Fin m → ℝ) (r c : ℝ)

/-- `W` vanishes when the weight vanishes on live fat boxes with `σ ≤ x`. -/
lemma W_zero_below (hm : 0 < m) (hr : 0 < r) (w : (Fin m → ℝ) → (Fin m → ℝ) → ℝ) (x : ℝ)
    (hw : ∀ lo hi, IsLive pts r c lo hi → Fat r lo hi → sigma lo hi ≤ x → w lo hi = 0) :
    ∀ f (lo hi : Fin m → ℝ), Adm pts r c lo hi → sigma lo hi ≤ x → W pts r c w f lo hi = 0 := by
  intro f
  induction f with
  | zero => intro lo hi _ _; rfl
  | succ f ih =>
    intro lo hi hA hx
    by_cases hl : IsLive pts r c lo hi
    · have hF := hA hl
      rw [W_succ_live pts r c w f hl, hw lo hi hl hF hx, zero_add]
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨B, hB, rfl⟩ := List.mem_map.1 hy
      exact ih _ _ (kids_adm pts r c hm hr hl hF B hB)
        ((kids_sigma_le pts r c hm hr hl hF B hB).trans hx)
    · exact W_notlive pts r c w _ hl

/-- Linear comparison of weighted counts. -/
lemma W_le_sum (hm : 0 < m) (hr : 0 < r) (w v0 : (Fin m → ℝ) → (Fin m → ℝ) → ℝ)
    (v : ℕ → (Fin m → ℝ) → (Fin m → ℝ) → ℝ) (s : Finset ℕ)
    (hw : ∀ lo hi, IsLive pts r c lo hi → Fat r lo hi → w lo hi ≤ v0 lo hi + ∑ k ∈ s, v k lo hi) :
    ∀ f (lo hi : Fin m → ℝ), Adm pts r c lo hi →
      W pts r c w f lo hi ≤ W pts r c v0 f lo hi + ∑ k ∈ s, W pts r c (v k) f lo hi := by
  intro f
  induction f with
  | zero => intro lo hi _; simp [W_zero]
  | succ f ih =>
    intro lo hi hA
    by_cases hl : IsLive pts r c lo hi
    · have hF := hA hl
      rw [W_succ_live pts r c w f hl, W_succ_live pts r c v0 f hl]
      simp_rw [W_succ_live pts r c _ f hl]
      rw [Finset.sum_add_distrib, ← list_sum_finset_swap]
      have h1 := hw lo hi hl hF
      have h2 : ((kids pts r lo hi).map fun B => W pts r c w f B.1 B.2).sum ≤
          ((kids pts r lo hi).map fun B => W pts r c v0 f B.1 B.2 +
            ∑ k ∈ s, W pts r c (v k) f B.1 B.2).sum := by
        apply List.sum_le_sum
        intro B hB
        exact ih _ _ (kids_adm pts r c hm hr hl hF B hB)
      rw [List.sum_map_add] at h2
      linarith
    · simp [W_notlive pts r c _ _ hl]

end W

/-! ## The chain potential -/

section Pot

variable (pts : Fin n → Fin m → ℝ) (r : ℝ)

/-- `ψ(x) = [λ ≤ x] + [2λ ≤ x]`. -/
noncomputable def psi (lam x : ℝ) : ℝ := (if lam ≤ x then 1 else 0) + (if 2 * lam ≤ x then 1 else 0)

lemma psi_nonneg (lam x : ℝ) : 0 ≤ psi lam x := by
  unfold psi; split_ifs <;> norm_num

lemma psi_le_two (lam x : ℝ) : psi lam x ≤ 2 := by
  unfold psi; split_ifs <;> norm_num

lemma psi_mono (lam : ℝ) {x y : ℝ} (h : x ≤ y) : psi lam x ≤ psi lam y := by
  unfold psi
  split_ifs <;> first | (exfalso; linarith) | norm_num

lemma psi_half (lam x : ℝ) (h0 : 0 < lam) (h1 : lam ≤ x) (h2 : x < 4 * lam) :
    psi lam (x / 2) + 1 = psi lam x := by
  unfold psi
  split_ifs <;> first | (exfalso; linarith) | norm_num

/-- `λ₀ = max (W - 2r) (16 r)` for the near set `N`. -/
noncomputable def lam0 (N : Finset (Fin n)) : ℝ := max (sigma (aLo pts N) (bHi pts N) - 2 * r) (16 * r)

open Classical in
/-- The chain potential. -/
noncomputable def piPot (N : Finset (Fin n)) (lo hi : Fin m → ℝ) : ℝ :=
  (if ∃ j, lo j < aLo pts N j - 2 * r ∨ bHi pts N j + 2 * r < hi j then 1 else 0) +
    ∑ j, psi (lam0 pts r N) (hi j - lo j)

lemma piPot_nonneg (N : Finset (Fin n)) (lo hi : Fin m → ℝ) : 0 ≤ piPot pts r N lo hi := by
  unfold piPot
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => psi_nonneg (lam0 pts r N) (hi j - lo j)
  split_ifs <;> linarith

lemma piPot_le (N : Finset (Fin n)) (lo hi : Fin m → ℝ) : piPot pts r N lo hi ≤ 2 * m + 1 := by
  unfold piPot
  have : ∑ j, psi (lam0 pts r N) (hi j - lo j) ≤ ∑ _j : Fin m, (2 : ℝ) :=
    Finset.sum_le_sum fun j _ => psi_le_two _ _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  split_ifs <;> linarith

end Pot

end DetANN.HPIM.BS

-- ===== BS_Top =====
namespace DetANN.HPIM.BS

open DetANN.HPIM

variable {m n : ℕ} (pts : Fin n → Fin m → ℝ) (r ε : ℝ)

section Top

variable (hm : 0 < m) (hr : 0 < r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)

include hm hr in
/-- Live kids of a live fat box with `σ > 16 r` have all sides `≥ r`. -/
lemma top_kids_sides {lo hi : Fin m → ℝ} (hl : IsLive pts r (1 + ε) lo hi) (hF : Fat r lo hi)
    (hσ : 16 * r < sigma lo hi) :
    ∀ B ∈ kids pts r lo hi, IsLive pts r (1 + ε) B.1 B.2 → ∀ j, r ≤ B.2 j - B.1 j := by
  rcases kids_cases pts r (1 + ε) hm hr hl hF with ⟨-, h⟩ | ⟨-, k, -, hk', h⟩
  · intro B hB hlB j
    rcases (h B hB).2 with h' | h'
    · exact absurd hlB (notLive_of_near_empty pts r _ h')
    · rw [h']
      have h6 := (core_props hr.le hl.1 hF.1 j).2.2.2.2.2.1
      refine le_trans ?_ h6
      have := hF.2 j
      rw [min_eq_right (by linarith : r ≤ sigma lo hi / 2)] at this
      exact le_min this le_rfl
  · rw [h]
    obtain ⟨f1, f2⟩ := split_kids_fat hm hF hk'
    obtain ⟨e1, e2⟩ := setCoord_side_k lo hi k
    intro B hB _ j
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    · have hs := le_sigma lo (setCoord hi k ((lo k + hi k) / 2)) k
      rw [e1, hk'] at hs
      have := f1.2 j
      rw [min_eq_right (by linarith : r ≤ sigma lo (setCoord hi k ((lo k + hi k) / 2)) / 2)] at this
      exact this
    · have hs := le_sigma (setCoord lo k ((lo k + hi k) / 2)) hi k
      rw [e2, hk'] at hs
      have := f2.2 j
      rw [min_eq_right (by linarith : r ≤ sigma (setCoord lo k ((lo k + hi k) / 2)) hi / 2)] at this
      exact this

include hm hr hε0 hε1 in
/-- A split half of a box with `σ > 16 r` is never an IN leaf. -/
lemma top_split_kid_live {lo hi : Fin m → ℝ} (hl : IsLive pts r (1 + ε) lo hi) (hF : Fat r lo hi)
    (hσ : 16 * r < sigma lo hi) (hc : ¬ Carves pts r lo hi) :
    ∀ B ∈ kids pts r lo hi, (nearS pts r B.1 B.2).Nonempty → IsLive pts r (1 + ε) B.1 B.2 := by
  obtain ⟨k, hk, hk'⟩ := longestAxis_some hm lo hi
  rw [kids_split pts r hc hk]
  obtain ⟨h1, h2, h3, h4⟩ := split_props hF.1 k
  obtain ⟨e1, e2⟩ := setCoord_side_k lo hi k
  intro B hB hN
  refine ⟨hN, ?_⟩
  rintro ⟨i, hi⟩
  unfold goodS at hi
  have hg := (Finset.mem_filter.1 hi).2
  have hside : 4 * r < (B.2 k - B.1 k) / 2 := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    · simp only; rw [e1, hk']; linarith
    · simp only; rw [e2, hk']; linarith
  have hle : B.1 k ≤ B.2 k := by linarith
  have := boxMaxDist2_ge_side B.1 B.2 (pts i) k hle
  have h4 : (4 * r) ^ 2 < ((B.2 k - B.1 k) / 2) ^ 2 := by
    apply pow_lt_pow_left₀ hside (by linarith) two_ne_zero
  have h5 : ((1 + ε) * r) ^ 2 ≤ (4 * r) ^ 2 := by
    apply pow_le_pow_left₀ (by nlinarith); nlinarith
  linarith

include hm hr hε0 hε1 in
/-- With a unique live kid, the near set does not change. -/
lemma top_near_eq {lo hi : Fin m → ℝ} (hl : IsLive pts r (1 + ε) lo hi) (hF : Fat r lo hi)
    (hσ : 16 * r < sigma lo hi) {C : (Fin m → ℝ) × (Fin m → ℝ)} (hC : C ∈ kids pts r lo hi)
    (hlC : IsLive pts r (1 + ε) C.1 C.2)
    (huniq : ∀ B ∈ kids pts r lo hi, IsLive pts r (1 + ε) B.1 B.2 → B = C) :
    nearS pts r C.1 C.2 = nearS pts r lo hi := by
  apply Finset.Subset.antisymm
  · have := kids_sub pts r (1 + ε) hm hr hl hF C hC
    exact nearS_mono pts r this.1 this.2
  · intro i hiN
    obtain ⟨B, hB, hiB⟩ := near_kids pts r hm hF.1 hiN
    suffices hlB : IsLive pts r (1 + ε) B.1 B.2 by rwa [huniq B hB hlB] at hiB
    by_cases hc : Carves pts r lo hi
    · rcases kids_cases pts r (1 + ε) hm hr hl hF with ⟨-, h⟩ | ⟨h, -⟩
      · rcases (h B hB).2 with h' | h'
        · rw [h'] at hiB; exact absurd hiB (Finset.notMem_empty _)
        · rcases (h C hC).2 with h'' | h''
          · exact absurd hlC (notLive_of_near_empty pts r _ h'')
          · rw [h', ← h'']; exact hlC
      · exact absurd hc h
    · exact top_split_kid_live pts r ε hm hr hε0 hε1 hl hF hσ hc B hB ⟨i, hiB⟩

include hm hr in
/-- The chain potential drops by at least one at a carve. -/
lemma piPot_core {lo hi : Fin m → ℝ} (hl : IsLive pts r (1 + ε) lo hi) (hF : Fat r lo hi)
    (hσ : 16 * r < sigma lo hi) (hc : Carves pts r lo hi) :
    piPot pts r (nearS pts r lo hi) (coreLo pts r lo hi) (coreHi pts r lo hi) + 1 ≤
      piPot pts r (nearS pts r lo hi) lo hi := by
  classical
  set N := nearS pts r lo hi
  have hC := (core_carveOK hr hl.1 hF.1).2
  -- the box carves somewhere
  have hcarv : ∃ j, lo j < aLo pts N j - 2 * r ∨ bHi pts N j + 2 * r < hi j := by
    by_contra hno
    push Not at hno
    have e1 : coreLo pts r lo hi = lo := funext fun j => max_eq_right (hno j).1
    have e2 : coreHi pts r lo hi = hi := funext fun j => min_eq_right (hno j).2
    unfold Carves at hc
    rw [e1, e2] at hc
    linarith
  have hnot : ¬ ∃ j, coreLo pts r lo hi j < aLo pts N j - 2 * r ∨
      bHi pts N j + 2 * r < coreHi pts r lo hi j := by
    rintro ⟨j, h | h⟩
    · have : aLo pts N j - 2 * r ≤ coreLo pts r lo hi j := le_max_left _ _
      linarith
    · have : coreHi pts r lo hi j ≤ bHi pts N j + 2 * r := min_le_left _ _
      linarith
  unfold piPot
  rw [if_pos hcarv, if_neg hnot, zero_add, add_comm]
  gcongr with j
  apply psi_mono
  linarith [(hC j).1, (hC j).2]

include hm hr in
/-- The chain potential drops by at least one at a split. -/
lemma piPot_split {lo hi : Fin m → ℝ} (hl : IsLive pts r (1 + ε) lo hi) (hF : Fat r lo hi)
    (hσ : 16 * r < sigma lo hi) (hc : ¬ Carves pts r lo hi) :
    ∀ B ∈ kids pts r lo hi, piPot pts r (nearS pts r lo hi) B.1 B.2 + 1 ≤
      piPot pts r (nearS pts r lo hi) lo hi := by
  classical
  set N := nearS pts r lo hi
  obtain ⟨k, hk, hk'⟩ := longestAxis_some hm lo hi
  rw [kids_split pts r hc hk]
  obtain ⟨e1, e2⟩ := setCoord_side_k lo hi k
  -- the window `λ₀ ≤ σ < 4 λ₀`
  set lam := lam0 pts r N
  have hW : sigma (aLo pts N) (bHi pts N) ≤ sigma lo hi + 2 * r := by
    apply sigma_le hm
    intro j
    have := aLo_ge pts r hr.le hl.1 j
    have := bHi_le pts r hr.le hl.1 j
    have := le_sigma lo hi j
    linarith
  have hT : sigma (coreLo pts r lo hi) (coreHi pts r lo hi) ≤ sigma (aLo pts N) (bHi pts N) + 4 * r := by
    apply sigma_le hm
    intro j
    have := (core_props hr.le hl.1 hF.1 j).2.2.2.2.2.2
    have := le_sigma (aLo pts N) (bHi pts N) j
    linarith
  have hlam1 : lam ≤ sigma lo hi := max_le (by linarith) hσ.le
  have hlam2 : sigma lo hi < 4 * lam := by
    unfold Carves at hc
    push Not at hc
    have := le_max_left (sigma (aLo pts N) (bHi pts N) - 2 * r) (16 * r)
    have := le_max_right (sigma (aLo pts N) (bHi pts N) - 2 * r) (16 * r)
    simp only [lam, lam0]
    linarith
  have hlam0 : 0 < lam := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hpsi := psi_half lam (sigma lo hi) hlam0 hlam1 hlam2
  -- generic: a kid that differs only in axis `k`, with side `σ/2` there
  have key : ∀ lo' hi' : Fin m → ℝ, (∀ j, lo j ≤ lo' j) → (∀ j, hi' j ≤ hi j) →
      (∀ j, j ≠ k → hi' j - lo' j = hi j - lo j) → hi' k - lo' k = sigma lo hi / 2 →
      piPot pts r N lo' hi' + 1 ≤ piPot pts r N lo hi := by
    intro lo' hi' h1 h2 h3 h4
    unfold piPot
    have hs : ∑ j, psi lam (hi' j - lo' j) + 1 ≤ ∑ j, psi lam (hi j - lo j) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
        h4, hk']
      have : ∑ j ∈ Finset.univ.erase k, psi lam (hi' j - lo' j) =
          ∑ j ∈ Finset.univ.erase k, psi lam (hi j - lo j) :=
        Finset.sum_congr rfl fun j hj => by rw [h3 j (Finset.ne_of_mem_erase hj)]
      rw [this]
      linarith
    have hif : (if ∃ j, lo' j < aLo pts N j - 2 * r ∨ bHi pts N j + 2 * r < hi' j then (1 : ℝ) else 0) ≤
        (if ∃ j, lo j < aLo pts N j - 2 * r ∨ bHi pts N j + 2 * r < hi j then 1 else 0) := by
      split_ifs with ha hb
      · exact le_rfl
      · exfalso; apply hb
        obtain ⟨j, hj⟩ := ha
        exact ⟨j, hj.imp (fun h => lt_of_le_of_lt (h1 j) h) (fun h => lt_of_lt_of_le h (h2 j))⟩
      · norm_num
      · exact le_rfl
    linarith
  obtain ⟨p1, p2, p3, p4⟩ := split_props hF.1 k
  intro B hB
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl
  · exact key _ _ (fun _ => le_rfl) p2 (fun j hj => by simp only; rw [setCoord_ne _ hj])
      (by simp only; rw [e1, hk'])
  · exact key _ _ p3 (fun _ => le_rfl) (fun j hj => by simp only; rw [setCoord_ne _ hj])
      (by simp only; rw [e2, hk'])

end Top


open Classical in
/-- Weight of the top scale. -/
noncomputable def wTop (r : ℝ) (lo hi : Fin m → ℝ) : ℝ := if 16 * r < sigma lo hi then 1 else 0

/-- Mass parameter of the top scale. -/
noncomputable def rhoT (m : ℕ) (r : ℝ) : ℝ := 2 * r ^ 2 + 2 * m * r ^ 2

/-- The normalized top mass. -/
noncomputable def mu (pts : Fin n → Fin m → ℝ) (r : ℝ) (lo hi : Fin m → ℝ) : ℝ :=
  mass pts (rhoT m r) lo hi / r ^ m

lemma mu_nonneg {r : ℝ} (hr : 0 < r) (lo hi : Fin m → ℝ) : 0 ≤ mu pts r lo hi := by
  unfold mu; exact div_nonneg (mass_nonneg _ _ _ _) (by positivity)

section Claim

variable (hm : 0 < m) (hr : 0 < r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)

include hm hr in
lemma mu_ge_one {lo hi : Fin m → ℝ} (hN : (nearS pts r lo hi).Nonempty) (hs : ∀ j, r ≤ hi j - lo j) :
    1 ≤ mu pts r lo hi := by
  unfold mu
  obtain ⟨i, hi⟩ := hN
  have := mass_ge hm pts hr hs ((mem_nearS pts r).1 hi)
  rw [le_div_iff₀ (by positivity), one_mul]
  exact this

lemma mu_cut {r : ℝ} (hr : 0 < r) (lo hi : Fin m → ℝ) (k : Fin m) (t : ℝ) (h1 : lo k ≤ t) (h2 : t ≤ hi k) :
    mu pts r lo (setCoord hi k t) + mu pts r (setCoord lo k t) hi ≤ mu pts r lo hi := by
  unfold mu
  rw [← add_div]
  exact div_le_div_of_nonneg_right (mass_cut pts _ lo hi k t h1 h2) (by positivity)

include hm hr hε0 hε1 in
/-- **The top claim**: for a live fat box with `σ > 16 r`,
`W_top + 2K ≤ 2K μ + 1 + Π`, `K = 2m + 2`. -/
theorem top_claim : ∀ f (lo hi : Fin m → ℝ), Adm pts r (1 + ε) lo hi → IsLive pts r (1 + ε) lo hi →
    16 * r < sigma lo hi →
    W pts r (1 + ε) (wTop r) f lo hi + 2 * (2 * m + 2) ≤
      2 * (2 * m + 2) * mu pts r lo hi + 1 + piPot pts r (nearS pts r lo hi) lo hi := by
  classical
  set K : ℝ := 2 * m + 2 with hK
  have hK0 : 0 < K := by positivity
  have hμ0 : ∀ lo hi, 0 ≤ mu pts r lo hi := fun lo hi => mu_nonneg pts hr lo hi
  -- sides of a fat box with σ > 16 r
  have hsides : ∀ lo hi : Fin m → ℝ, Fat r lo hi → 16 * r < sigma lo hi → ∀ j, r ≤ hi j - lo j := by
    intro lo hi hF hσ j
    have := hF.2 j
    rwa [min_eq_right (by linarith : r ≤ sigma lo hi / 2)] at this
  intro f
  induction f with
  | zero =>
    intro lo hi hA hl hσ
    have h1 := mu_ge_one pts r hm hr hl.1 (hsides lo hi (hA hl) hσ)
    have h2 := piPot_nonneg pts r (nearS pts r lo hi) lo hi
    rw [W_zero]
    nlinarith
  | succ f ih =>
    intro lo hi hA hl hσ
    have hF := hA hl
    rw [W_succ_live pts r _ _ f hl]
    simp only [wTop, if_pos hσ]
    set L := kids pts r lo hi with hL
    set X : (Fin m → ℝ) × (Fin m → ℝ) → ℝ := fun B => W pts r (1 + ε) (wTop r) f B.1 B.2 with hX
    have hμB := mu_ge_one pts r hm hr hl.1 (hsides lo hi hF hσ)
    have hPB := piPot_nonneg pts r (nearS pts r lo hi) lo hi
    -- superadditivity of μ
    have hsup : (L.map fun B => mu pts r B.1 B.2).sum ≤ mu pts r lo hi :=
      kids_sum_le pts r (1 + ε) hm hr hl hF (mu pts r) (mu_cut pts hr)
    -- the per-kid facts
    have hlow : ∀ B ∈ L, IsLive pts r (1 + ε) B.1 B.2 → sigma B.1 B.2 ≤ 16 * r → X B = 0 := by
      intro B hB _ hs
      exact W_zero_below pts r (1 + ε) hm hr (wTop r) (16 * r)
        (fun lo hi _ _ h => by simp only [wTop]; rw [if_neg (not_lt.2 h)]) f B.1 B.2
        (kids_adm pts r (1 + ε) hm hr hl hF B hB) hs
    have hμC : ∀ B ∈ L, IsLive pts r (1 + ε) B.1 B.2 → 1 ≤ mu pts r B.1 B.2 := fun B hB hlB =>
      mu_ge_one pts r hm hr hlB.1 (top_kids_sides pts r ε hm hr hl hF hσ B hB hlB)
    have hbd : ∀ B ∈ L, IsLive pts r (1 + ε) B.1 B.2 → X B ≤ K * (2 * mu pts r B.1 B.2) - K := by
      intro B hB hlB
      by_cases hs : sigma B.1 B.2 ≤ 16 * r
      · rw [hlow B hB hlB hs]
        have := hμC B hB hlB
        nlinarith
      · push Not at hs
        have h1 := ih B.1 B.2 (kids_adm pts r (1 + ε) hm hr hl hF B hB) hlB hs
        have h2 := piPot_le pts r (nearS pts r B.1 B.2) B.1 B.2
        nlinarith
    -- restrict to the live kids
    set Lv := L.filter fun B => IsLive pts r (1 + ε) B.1 B.2 with hLv
    have hmemLv : ∀ B, B ∈ Lv ↔ B ∈ L ∧ IsLive pts r (1 + ε) B.1 B.2 := fun B => by
      simp [hLv, List.mem_filter]
    have hsumX : (L.map X).sum = (Lv.map X).sum :=
      list_sum_map_filter L _ X fun B hB hn => W_notlive pts r _ _ _ hn
    have hsumμ : (Lv.map fun B => mu pts r B.1 B.2).sum ≤ (L.map fun B => mu pts r B.1 B.2).sum :=
      list_sum_filter_le L _ _ fun B _ => hμ0 _ _
    have hbound : (Lv.map X).sum ≤ K * (Lv.map fun B => 2 * mu pts r B.1 B.2).sum - K * Lv.length :=
      list_sum_le_mul_length Lv X (fun B => 2 * mu pts r B.1 B.2) K fun B hB =>
        hbd B ((hmemLv B).1 hB).1 ((hmemLv B).1 hB).2
    have h2μ : (Lv.map fun B => 2 * mu pts r B.1 B.2).sum = 2 * (Lv.map fun B => mu pts r B.1 B.2).sum := by
      rw [← List.sum_map_mul_left]
    rw [hsumX]
    rcases Nat.lt_or_ge Lv.length 2 with hlen | hlen
    · rcases Nat.lt_or_ge Lv.length 1 with hlen' | hlen'
      · -- no live kid
        have : Lv = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this]; simp only [List.map_nil, List.sum_nil]
        nlinarith
      · -- exactly one live kid
        obtain ⟨C, hC⟩ := List.length_eq_one_iff.1 (by omega : Lv.length = 1)
        have hCm := (hmemLv C).1 (by rw [hC]; exact List.mem_singleton_self _)
        rw [hC]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        have hμCB : mu pts r C.1 C.2 ≤ mu pts r lo hi := by
          have := hsumμ; rw [hC] at this
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at this
          linarith
        by_cases hs : sigma C.1 C.2 ≤ 16 * r
        · rw [hlow C hCm.1 hCm.2 hs]; nlinarith
        · push Not at hs
          have huniq : ∀ B ∈ L, IsLive pts r (1 + ε) B.1 B.2 → B = C := by
            intro B hB hlB
            have : B ∈ Lv := (hmemLv B).2 ⟨hB, hlB⟩
            rw [hC] at this; exact List.mem_singleton.1 this
          have hnear := top_near_eq pts r ε hm hr hε0 hε1 hl hF hσ hCm.1 hCm.2 huniq
          have h1 := ih C.1 C.2 (kids_adm pts r (1 + ε) hm hr hl hF C hCm.1) hCm.2 hs
          rw [hnear] at h1
          have hdec : piPot pts r (nearS pts r lo hi) C.1 C.2 + 1 ≤
              piPot pts r (nearS pts r lo hi) lo hi := by
            by_cases hc : Carves pts r lo hi
            · rcases kids_cases pts r (1 + ε) hm hr hl hF with ⟨-, h⟩ | ⟨h, -⟩
              · rcases (h C hCm.1).2 with h' | h'
                · exact absurd hCm.2 (notLive_of_near_empty pts r _ h')
                · rw [h']; exact piPot_core pts r ε hm hr hl hF hσ hc
              · exact absurd hc h
            · exact piPot_split pts r ε hm hr hl hF hσ hc C hCm.1
          nlinarith
    · -- at least two live kids
      have hlenR : (2 : ℝ) ≤ Lv.length := by exact_mod_cast hlen
      rw [h2μ] at hbound
      nlinarith

end Claim

end DetANN.HPIM.BS

-- ===== BS_Low =====
namespace DetANN.HPIM.BS

open DetANN.HPIM

variable {m n : ℕ} (pts : Fin n → Fin m → ℝ) (r ε : ℝ)

open Classical in
/-- Weight of the class `(s/2, s]`. -/
noncomputable def wC (s : ℝ) (lo hi : Fin m → ℝ) : ℝ :=
  if s / 2 < sigma lo hi ∧ sigma lo hi ≤ s then 1 else 0

open Classical in
/-- Number of long sides (`> s/2`). -/
noncomputable def eLong (s : ℝ) (lo hi : Fin m → ℝ) : ℕ :=
  (Finset.univ.filter fun j : Fin m => s / 2 < hi j - lo j).card

open Classical in
/-- The class budget. -/
noncomputable def EB (s : ℝ) (lo hi : Fin m → ℝ) : ℝ :=
  if sigma lo hi ≤ s then (eLong s lo hi : ℝ) + 1 else m + 1

lemma eLong_le (s : ℝ) (lo hi : Fin m → ℝ) : eLong s lo hi ≤ m := by
  unfold eLong
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma EB_le (s : ℝ) (lo hi : Fin m → ℝ) : EB s lo hi ≤ m + 1 := by
  unfold EB
  have : (eLong s lo hi : ℝ) ≤ m := by exact_mod_cast eLong_le s lo hi
  split_ifs <;> linarith

lemma EB_ge (s : ℝ) (lo hi : Fin m → ℝ) : 1 ≤ EB s lo hi := by
  unfold EB
  split_ifs
  · have : (0 : ℝ) ≤ eLong s lo hi := Nat.cast_nonneg _
    linarith
  · have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith

/-- Mass parameter of the class `s`. -/
noncomputable def rhoC (m : ℕ) (r s : ℝ) : ℝ := 2 * r ^ 2 + 2 * m * (s / 32) ^ 2

section Class

variable (hm : 0 < m) (hr : 0 < r) (s : ℝ) (hs : 0 < s) (hs16 : s ≤ 16 * r)

include hm hr hs hs16 in
/-- **The class claim**: `W_s · (s/32)^m ≤ E · mass`. -/
theorem class_claim : ∀ f (lo hi : Fin m → ℝ), Adm pts r (1 + ε) lo hi →
    W pts r (1 + ε) (wC s) f lo hi * (s / 32) ^ m ≤ EB s lo hi * mass pts (rhoC m r s) lo hi := by
  classical
  have hmass0 : ∀ lo hi, 0 ≤ mass pts (rhoC m r s) lo hi := fun lo hi => mass_nonneg _ _ _ _
  have hlam : (0 : ℝ) < (s / 32) ^ m := by positivity
  intro f
  induction f with
  | zero =>
    intro lo hi _
    rw [W_zero, zero_mul]
    exact mul_nonneg (le_trans zero_le_one (EB_ge s lo hi)) (hmass0 _ _)
  | succ f ih =>
    intro lo hi hA
    by_cases hl : IsLive pts r (1 + ε) lo hi
    swap
    · rw [W_notlive pts r _ _ _ hl, zero_mul]
      exact mul_nonneg (le_trans zero_le_one (EB_ge s lo hi)) (hmass0 _ _)
    have hF := hA hl
    have hsup : ((kids pts r lo hi).map fun B => mass pts (rhoC m r s) B.1 B.2).sum ≤
        mass pts (rhoC m r s) lo hi :=
      kids_sum_le pts r (1 + ε) hm hr hl hF _ (mass_cut pts _)
    -- below the class
    by_cases hlow : sigma lo hi ≤ s / 2
    · rw [W_zero_below pts r (1 + ε) hm hr (wC s) (s / 2)
        (fun lo hi _ _ h => by unfold wC; rw [if_neg (fun h' => by linarith [h'.1])]) (f + 1) lo hi
        hA hlow, zero_mul]
      exact mul_nonneg (le_trans zero_le_one (EB_ge s lo hi)) (hmass0 _ _)
    push Not at hlow
    rw [W_succ_live pts r _ _ f hl, add_mul, ← List.sum_map_mul_right]
    by_cases hin : sigma lo hi ≤ s
    · -- in the class
      have hw : wC s lo hi = 1 := by unfold wC; rw [if_pos ⟨hlow, hin⟩]
      have hE : EB s lo hi = eLong s lo hi + 1 := by unfold EB; rw [if_pos hin]
      rw [hw, one_mul, hE]
      -- the mass of the box itself
      have hsides : ∀ j, s / 32 ≤ hi j - lo j := by
        intro j
        refine le_trans ?_ (hF.2 j)
        exact le_min (by linarith) (by linarith)
      obtain ⟨i, hiN⟩ := hl.1
      have hself := mass_ge hm pts (by positivity : (0:ℝ) < s / 32) hsides ((mem_nearS pts r).1 hiN)
      have hself' : (s / 32) ^ m ≤ mass pts (rhoC m r s) lo hi := hself
      rcases kids_cases pts r (1 + ε) hm hr hl hF with ⟨hc, h⟩ | ⟨hc, k, hk, hk', h⟩
      · -- carve: no class node below
        have hz : ((kids pts r lo hi).map fun B => W pts r (1 + ε) (wC s) f B.1 B.2 * (s / 32) ^ m).sum
            = 0 := by
          refine List.sum_eq_zero fun y hy => ?_
          obtain ⟨B, hB, rfl⟩ := List.mem_map.1 hy
          rcases (h B hB).2 with h' | h'
          · rw [W_notlive pts r _ _ _ (notLive_of_near_empty pts r _ h'), zero_mul]
          · have hσT : sigma B.1 B.2 ≤ s / 2 := by
              rw [h']; unfold Carves at hc; linarith
            rw [W_zero_below pts r (1 + ε) hm hr (wC s) (s / 2)
              (fun lo hi _ _ h => by unfold wC; rw [if_neg (fun h' => by linarith [h'.1])]) f _ _
              (kids_adm pts r (1 + ε) hm hr hl hF B hB) hσT, zero_mul]
        rw [hz, add_zero]
        have : (0 : ℝ) ≤ eLong s lo hi := Nat.cast_nonneg _
        nlinarith [hmass0 lo hi]
      · -- split: every kid has one long side less
        have hkid : ∀ B ∈ kids pts r lo hi, EB s B.1 B.2 ≤ eLong s lo hi := by
          intro B hB
          have hσB := (kids_sigma_le pts r (1 + ε) hm hr hl hF B hB).trans hin
          unfold EB; rw [if_pos hσB]
          have hsub := kids_sub pts r (1 + ε) hm hr hl hF B hB
          have hBk : B.2 k - B.1 k = sigma lo hi / 2 := by
            obtain ⟨e1, e2⟩ := setCoord_side_k lo hi k
            rw [h] at hB
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hB
            rcases hB with rfl | rfl
            · simp only; rw [e1, hk']
            · simp only; rw [e2, hk']
          have hk_mem : k ∈ Finset.univ.filter fun j : Fin m => s / 2 < hi j - lo j :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hk']; exact hlow⟩
          have hsubset : (Finset.univ.filter fun j : Fin m => s / 2 < B.2 j - B.1 j) ⊆
              (Finset.univ.filter fun j : Fin m => s / 2 < hi j - lo j).erase k := by
            intro j hj
            have hj' := (Finset.mem_filter.1 hj).2
            refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
            · rintro rfl; rw [hBk] at hj'; linarith
            · linarith [hsub.1 j, hsub.2 j]
          have hc := Finset.card_le_card hsubset
          rw [Finset.card_erase_of_mem hk_mem] at hc
          have hpos : 0 < (Finset.univ.filter fun j : Fin m => s / 2 < hi j - lo j).card :=
            Finset.card_pos.2 ⟨k, hk_mem⟩
          unfold eLong
          have : ((Finset.univ.filter fun j : Fin m => s / 2 < B.2 j - B.1 j).card : ℝ) + 1 ≤
              ((Finset.univ.filter fun j : Fin m => s / 2 < hi j - lo j).card : ℝ) := by
            exact_mod_cast (by omega : (Finset.univ.filter fun j : Fin m => s / 2 < B.2 j - B.1 j).card
              + 1 ≤ (Finset.univ.filter fun j : Fin m => s / 2 < hi j - lo j).card)
          exact this
        have hsum : ((kids pts r lo hi).map fun B => W pts r (1 + ε) (wC s) f B.1 B.2 * (s / 32) ^ m).sum
            ≤ ((kids pts r lo hi).map fun B => (eLong s lo hi : ℝ) *
                mass pts (rhoC m r s) B.1 B.2).sum := by
          apply List.sum_le_sum
          intro B hB
          exact (ih B.1 B.2 (kids_adm pts r (1 + ε) hm hr hl hF B hB)).trans
            (mul_le_mul_of_nonneg_right (hkid B hB) (hmass0 _ _))
        rw [List.sum_map_mul_left] at hsum
        have : (0 : ℝ) ≤ eLong s lo hi := Nat.cast_nonneg _
        nlinarith
    · -- above the class
      push Not at hin
      have hw : wC s lo hi = 0 := by unfold wC; rw [if_neg (fun h' => by linarith [h'.2])]
      have hE : EB s lo hi = m + 1 := by unfold EB; rw [if_neg (not_le.2 hin)]
      rw [hw, zero_mul, zero_add, hE]
      have hsum : ((kids pts r lo hi).map fun B => W pts r (1 + ε) (wC s) f B.1 B.2 * (s / 32) ^ m).sum
          ≤ ((kids pts r lo hi).map fun B => ((m : ℝ) + 1) * mass pts (rhoC m r s) B.1 B.2).sum := by
        apply List.sum_le_sum
        intro B hB
        exact (ih B.1 B.2 (kids_adm pts r (1 + ε) hm hr hl hF B hB)).trans
          (mul_le_mul_of_nonneg_right (EB_le s _ _) (hmass0 _ _))
      rw [List.sum_map_mul_left] at hsum
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      nlinarith

end Class

end DetANN.HPIM.BS

-- ===== BS_Final =====
namespace DetANN.HPIM.BS

open DetANN.HPIM

variable {m n : ℕ}

/-! ## The root box is fat -/

lemma root_fat (hn : 0 < n) (pts : Fin n → Fin m → ℝ) {r : ℝ} (hr : 0 < r) (hm : 0 < m) :
    Fat r (rootLo hn pts r) (rootHi hn pts r) := by
  set A : Fin m → ℝ := fun j => Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j)
  set B : Fin m → ℝ := fun j => Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => pts i j)
  have hAB : ∀ j, A j ≤ B j := fun j =>
    (Finset.inf'_le _ (Finset.mem_univ ⟨0, hn⟩)).trans (Finset.le_sup' (fun i => pts i j) (Finset.mem_univ _))
  have hD : 0 ≤ sigma A B := sigma_nonneg hm hAB
  have hlo : rootLo hn pts r = fun j => A j - (sigma A B + 4 * r) := rfl
  have hhi : rootHi hn pts r = fun j => B j + (sigma A B + 4 * r) := rfl
  have hside : ∀ j, rootHi hn pts r j - rootLo hn pts r j = B j - A j + 2 * (sigma A B + 4 * r) := by
    intro j; rw [hlo, hhi]; ring
  have hσ : sigma (rootLo hn pts r) (rootHi hn pts r) ≤ 3 * sigma A B + 8 * r := by
    apply sigma_le hm
    intro j; rw [hside]; have := le_sigma A B j; linarith
  refine ⟨fun j => by have := hside j; have := hAB j; linarith, fun j => ?_⟩
  refine (min_le_left _ _).trans ?_
  rw [hside]
  have := hAB j
  linarith

/-! ## Classes -/

lemma sum_sq_le (hm : 0 < m) {lo hi : Fin m → ℝ} (hle : ∀ j, lo j ≤ hi j) :
    ∑ j, (hi j - lo j) ^ 2 ≤ m * sigma lo hi ^ 2 := by
  have : ∀ j ∈ Finset.univ, (hi j - lo j) ^ 2 ≤ sigma lo hi ^ 2 := fun j _ =>
    pow_le_pow_left₀ (by linarith [hle j]) (le_sigma lo hi j) 2
  have h := Finset.sum_le_card_nsmul Finset.univ _ _ this
  simpa using h

/-- The scale of class `k`. -/
noncomputable def sc (r : ℝ) (k : ℕ) : ℝ := 16 * r / 2 ^ k

lemma sc_pos {r : ℝ} (hr : 0 < r) (k : ℕ) : 0 < sc r k := by unfold sc; positivity

lemma sc_le {r : ℝ} (hr : 0 < r) (k : ℕ) : sc r k ≤ 16 * r := by
  unfold sc
  rw [div_le_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  nlinarith

/-- The number of classes. -/
noncomputable def nCls (m : ℕ) (ε : ℝ) : ℕ := ⌈16 * (m : ℝ) / ε⌉₊

section Classes

variable (pts : Fin n → Fin m → ℝ) (r ε : ℝ) (hm : 0 < m) (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
include hm hr hε0 hε1

/-- Every live fat box of the low scales lies in one of the first `nCls` classes. -/
lemma exists_class {lo hi : Fin m → ℝ} (hl : IsLive pts r (1 + ε) lo hi) (hF : Fat r lo hi)
    (hσ : sigma lo hi ≤ 16 * r) : ∃ k ∈ Finset.range (nCls m ε), wC (sc r k) lo hi = 1 := by
  classical
  have h3 := live_not_small hF.1 hr hε0.le hl
  have hsq := sum_sq_le hm hF.1
  have hσ0 : 0 < sigma lo hi := by
    by_contra h
    push Not at h
    have : sigma lo hi ^ 2 = 0 ∨ True := Or.inr trivial
    have hs : sigma lo hi = 0 ∨ sigma lo hi < 0 := by
      rcases h.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hl0 := le_sigma lo hi ⟨0, hm⟩
    have hz : ∀ j, hi j - lo j = 0 := fun j => le_antisymm ((le_sigma lo hi j).trans h)
      (by linarith [hF.1 j])
    have : ∑ j, (hi j - lo j) ^ 2 = 0 := by simp [hz]
    nlinarith
  have hex : ∃ k : ℕ, sc r (k + 1) < sigma lo hi := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < sigma lo hi / (16 * r))
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨k, ?_⟩
    unfold sc
    rw [div_lt_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hk
    have : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
    have h2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h2]
    have hpos : (0 : ℝ) < 2 ^ k := by positivity
    nlinarith
  set k := Nat.find hex with hkdef
  have hk1 : sc r (k + 1) < sigma lo hi := Nat.find_spec hex
  have hk2 : sigma lo hi ≤ sc r k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; unfold sc; simpa using hσ
    · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have := Nat.find_min hex (by omega : k' < k)
      push Not at this
      rw [hk']; exact this
  have hhalf : sc r k / 2 = sc r (k + 1) := by unfold sc; rw [pow_succ]; field_simp
  refine ⟨k, Finset.mem_range.2 ?_, ?_⟩
  · -- the class is not too deep
    by_contra hge
    push Not at hge
    have hN : 16 * (m : ℝ) / ε ≤ k := (Nat.le_ceil _).trans (Nat.cast_le.2 hge)
    have hk2' : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    have hs : sigma lo hi ^ 2 ≤ sc r k ^ 2 := pow_le_pow_left₀ hσ0.le hk2 2
    have hsc : sc r k * 2 ^ k = 16 * r := by unfold sc; field_simp
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have h1 : 16 * m < ε * 2 ^ k := by
      rw [div_le_iff₀ hε0] at hN
      nlinarith
    -- (ε r)^2 < m σ^2 ≤ m sc^2, and ε 2^k > 16 m
    have h4 : (ε * r) ^ 2 < m * sc r k ^ 2 := by nlinarith
    have h5 : (ε * r * 2 ^ k) ^ 2 < m * (16 * r) ^ 2 := by
      have hp : (0:ℝ) < (2 ^ k) ^ 2 := by positivity
      have := mul_lt_mul_of_pos_right h4 hp
      calc (ε * r * 2 ^ k) ^ 2 = (ε * r) ^ 2 * (2 ^ k) ^ 2 := by ring
        _ < m * sc r k ^ 2 * (2 ^ k) ^ 2 := this
        _ = m * (sc r k * 2 ^ k) ^ 2 := by ring
        _ = m * (16 * r) ^ 2 := by rw [hsc]
    have h6 : (16 * m * r) ^ 2 < (ε * r * 2 ^ k) ^ 2 :=
      pow_lt_pow_left₀ (by nlinarith) (by positivity) two_ne_zero
    have h7 : (16 * m * r) ^ 2 < m * (16 * r) ^ 2 := h6.trans h5
    have h8 : (16 * m * r) ^ 2 - m * (16 * r) ^ 2 = 256 * r ^ 2 * m * (m - 1) := by ring
    have h9 : 0 ≤ 256 * r ^ 2 * m * (m - 1) := by
      have : (0:ℝ) ≤ m - 1 := by linarith
      positivity
    linarith
  · unfold wC; rw [if_pos ⟨by rw [hhalf]; exact hk1, hk2⟩]

/-- Classes with `m s^2 ≤ (ε r)^2` are empty. -/
lemma class_empty (k : ℕ) (hk : m * sc r k ^ 2 ≤ (ε * r) ^ 2) {lo hi : Fin m → ℝ}
    (hl : IsLive pts r (1 + ε) lo hi) (hF : Fat r lo hi) : wC (sc r k) lo hi = 0 := by
  unfold wC
  rw [if_neg]
  rintro ⟨h1, h2⟩
  have h3 := live_not_small hF.1 hr hε0.le hl
  have hsq := sum_sq_le hm hF.1
  have hσ0 : 0 ≤ sigma lo hi := sigma_nonneg hm hF.1
  have : sigma lo hi ^ 2 ≤ sc r k ^ 2 := pow_le_pow_left₀ hσ0 h2 2
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith

end Classes


lemma sqrt_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ y ^ 2) (m : ℕ) :
    Real.sqrt (x ^ m) ≤ y ^ m := by
  calc Real.sqrt (x ^ m) ≤ Real.sqrt ((y ^ 2) ^ m) := Real.sqrt_le_sqrt (pow_le_pow_left₀ hx h m)
    _ = y ^ m := by rw [← pow_mul, mul_comm, pow_mul, Real.sqrt_sq (pow_nonneg hy m)]

section Root

variable (hn : 0 < n) (pts : Fin n → Fin m → ℝ) (r ε : ℝ) (hm : 0 < m) (hr : 0 < r) (hε0 : 0 < ε)
  (hε1 : ε ≤ 1)
include hm hr hε0 hε1

lemma root_top_bound (f : ℕ) :
    W pts r (1 + ε) (wTop r) f (rootLo hn pts r) (rootHi hn pts r) ≤ 2 * (2 * m + 2) * (n * 9 ^ m) := by
  set lo := rootLo hn pts r
  set hi := rootHi hn pts r
  have hF := root_fat hn pts hr hm
  have hA : Adm pts r (1 + ε) lo hi := fun _ => hF
  have hK : (0 : ℝ) ≤ 2 * (2 * m + 2) * (n * 9 ^ m) := by positivity
  by_cases hl : IsLive pts r (1 + ε) lo hi
  swap; · rw [W_notlive pts r _ _ _ hl]; exact hK
  by_cases hσ : 16 * r < sigma lo hi
  swap
  · rw [W_zero_below pts r (1 + ε) hm hr (wTop r) (16 * r)
      (fun lo hi _ _ h => by unfold wTop; rw [if_neg (not_lt.2 h)]) f lo hi hA (not_lt.1 hσ)]
    exact hK
  have h1 := top_claim pts r ε hm hr hε0.le hε1 f lo hi hA hl hσ
  have h2 := piPot_le pts r (nearS pts r lo hi) lo hi
  have h3 : mu pts r lo hi ≤ n * 9 ^ m := by
    unfold mu
    rw [div_le_iff₀ (by positivity)]
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hρ : 0 < rhoT m r := by unfold rhoT; positivity
    refine (mass_le hm pts hρ lo hi).trans ?_
    have h4 : Real.sqrt ((18 * rhoT m r / m) ^ m) ≤ (9 * r) ^ m := by
      apply sqrt_pow_le (by positivity) (by positivity)
      unfold rhoT
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg r]
    calc (n : ℝ) * Real.sqrt ((18 * rhoT m r / m) ^ m) ≤ n * (9 * r) ^ m :=
          mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
      _ = n * 9 ^ m * r ^ m := by rw [mul_pow]; ring
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith

lemma root_class_bound (f k : ℕ) :
    W pts r (1 + ε) (wC (sc r k)) f (rootLo hn pts r) (rootHi hn pts r) ≤
      (m + 1) * (n * (193 / ε) ^ m) := by
  set lo := rootLo hn pts r
  set hi := rootHi hn pts r
  have hF := root_fat hn pts hr hm
  have hA : Adm pts r (1 + ε) lo hi := fun _ => hF
  have hK : (0 : ℝ) ≤ (m + 1) * (n * (193 / ε) ^ m) := by positivity
  by_cases hk : m * sc r k ^ 2 ≤ (ε * r) ^ 2
  · rw [W_zero_below pts r (1 + ε) hm hr (wC (sc r k)) (sigma lo hi)
      (fun lo hi hl hF _ => class_empty pts r ε hm hr hε0 hε1 k hk hl hF) f lo hi hA le_rfl]
    exact hK
  push Not at hk
  set s := sc r k
  have hs := sc_pos hr k
  have h1 := class_claim pts r ε hm hr s hs (sc_le hr k) f lo hi hA
  have hlam : (0 : ℝ) < (s / 32) ^ m := by positivity
  have hρ : 0 < rhoC m r s := by unfold rhoC; positivity
  have h2 := mass_le hm pts hρ lo hi
  have h3 : Real.sqrt ((18 * rhoC m r s / m) ^ m) ≤ (193 * (s / 32) / ε) ^ m := by
    apply sqrt_pow_le (by positivity) (by positivity)
    unfold rhoC
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    -- r^2 < m s^2 / ε^2
    have hr2 : r ^ 2 * ε ^ 2 < m * s ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have e : (193 * (s / 32) / ε) ^ 2 * m = (193 ^ 2 * (s / 32) ^ 2 * m) / ε ^ 2 := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith
    have hms : (0 : ℝ) ≤ m * (s / 32) ^ 2 := by positivity
    nlinarith
  have hE := EB_le s lo hi
  have h4 : W pts r (1 + ε) (wC s) f lo hi * (s / 32) ^ m ≤
      (m + 1) * (n * (193 / ε) ^ m) * (s / 32) ^ m := by
    calc W pts r (1 + ε) (wC s) f lo hi * (s / 32) ^ m
        ≤ EB s lo hi * mass pts (rhoC m r s) lo hi := h1
      _ ≤ (m + 1) * (n * Real.sqrt ((18 * rhoC m r s / m) ^ m)) :=
          mul_le_mul hE h2 (mass_nonneg _ _ _ _) (by positivity)
      _ ≤ (m + 1) * (n * (193 * (s / 32) / ε) ^ m) := by gcongr
      _ = (m + 1) * (n * (193 / ε) ^ m) * (s / 32) ^ m := by
          rw [show 193 * (s / 32) / ε = (193 / ε) * (s / 32) by ring, mul_pow]; ring
  exact le_of_mul_le_mul_right h4 hlam

lemma root_count_bound (f : ℕ) :
    W pts r (1 + ε) (fun _ _ => 1) f (rootLo hn pts r) (rootHi hn pts r) ≤
      2 * (2 * m + 2) * (n * 9 ^ m) + nCls m ε * ((m + 1) * (n * (193 / ε) ^ m)) := by
  classical
  have hF := root_fat hn pts hr hm
  have h := W_le_sum pts r (1 + ε) hm hr (fun _ _ => 1) (wTop r) (fun k => wC (sc r k))
    (Finset.range (nCls m ε)) (fun lo hi hl hF => by
      have hnn : ∀ k ∈ Finset.range (nCls m ε), 0 ≤ wC (sc r k) lo hi := fun k _ => by
        unfold wC; split_ifs <;> norm_num
      by_cases hσ : 16 * r < sigma lo hi
      · have : wTop r lo hi = 1 := by unfold wTop; rw [if_pos hσ]
        rw [this]
        linarith [Finset.sum_nonneg hnn]
      · obtain ⟨k, hk, hk1⟩ := exists_class pts r ε hm hr hε0 hε1 hl hF (not_lt.1 hσ)
        have h0 : 0 ≤ wTop r lo hi := by unfold wTop; split_ifs <;> norm_num
        have := Finset.single_le_sum hnn hk
        rw [hk1] at this
        linarith) f _ _ (fun _ => hF)
  refine h.trans (add_le_add (root_top_bound hn pts r ε hm hr hε0 hε1 f) ?_)
  calc ∑ k ∈ Finset.range (nCls m ε), W pts r (1 + ε) (wC (sc r k)) f (rootLo hn pts r) (rootHi hn pts r)
      ≤ ∑ _k ∈ Finset.range (nCls m ε), (m + 1) * (n * (193 / ε) ^ m) :=
        Finset.sum_le_sum fun k _ => root_class_bound hn pts r ε hm hr hε0 hε1 f k
    _ = nCls m ε * ((m + 1) * (n * (193 / ε) ^ m)) := by simp

end Root

/-! ## Arithmetic -/

lemma nat_poly_le (m : ℕ) : (m : ℝ) ≤ 2 ^ m ∧ (m : ℝ) + 1 ≤ 2 ^ m := by
  have h : m < 2 ^ m := Nat.lt_two_pow_self
  constructor
  · exact_mod_cast h.le
  · exact_mod_cast h

lemma final_arith (hm : 0 < m) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (nR : ℝ) (hn : 0 ≤ nR) :
    2 * m * (2 * (2 * m + 2) * (nR * 9 ^ m) + (16 * m / ε + 1) * ((m + 1) * (nR * (193 / ε) ^ m))) ≤
      nR * (2 ^ 12 / ε) ^ (2 * m) := by
  set t := 1 / ε with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hε0]; linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨p1, p2⟩ := nat_poly_le m
  have e1 : 193 / ε = 193 * t := by rw [ht]; ring
  have e2 : 2 ^ 12 / ε = 2 ^ 12 * t := by rw [ht]; ring
  have e3 : 16 * m / ε + 1 ≤ 17 * m * t := by
    have : (1 : ℝ) ≤ m * t := by nlinarith
    rw [ht]; rw [ht] at this; field_simp; field_simp at this; nlinarith
  rw [e1, e2, mul_pow, mul_pow]
  -- powers of t
  have tm : 1 ≤ t ^ m := one_le_pow₀ ht1
  have t2m : t ^ (m + 1) ≤ t ^ (2 * m) := pow_le_pow_right₀ ht1 (by omega)
  have t1 : 1 ≤ t ^ (2 * m) := one_le_pow₀ ht1
  -- the bracket
  have hb : 8 * (m * (m + 1)) * 9 ^ m + 34 * (m * m * (m + 1)) * 193 ^ m ≤ ((2 : ℝ) ^ 12) ^ (2 * m) := by
    have q1 : (m : ℝ) * (m + 1) ≤ 4 ^ m := by
      calc (m : ℝ) * (m + 1) ≤ 2 ^ m * 2 ^ m := mul_le_mul p1 p2 (by positivity) (by positivity)
        _ = 4 ^ m := by rw [← mul_pow]; norm_num
    have q2 : (m : ℝ) * m * (m + 1) ≤ 8 ^ m := by
      calc (m : ℝ) * m * (m + 1) ≤ 2 ^ m * 2 ^ m * 2 ^ m :=
            mul_le_mul (mul_le_mul p1 p1 (by positivity) (by positivity)) p2 (by positivity) (by positivity)
        _ = 8 ^ m := by rw [← mul_pow, ← mul_pow]; norm_num
    have q3 : (36 : ℝ) ^ m ≤ 1544 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
    have q4 : (42 : ℝ) ≤ 42 ^ m := by
      calc (42 : ℝ) = 42 ^ 1 := by norm_num
        _ ≤ 42 ^ m := pow_le_pow_right₀ (by norm_num) hm
    have q5 : (42 : ℝ) ^ m * 1544 ^ m ≤ ((2 : ℝ) ^ 12) ^ (2 * m) := by
      rw [← mul_pow, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
    calc (8 : ℝ) * (m * (m + 1)) * 9 ^ m + 34 * (m * m * (m + 1)) * 193 ^ m
        ≤ 8 * 4 ^ m * 9 ^ m + 34 * 8 ^ m * 193 ^ m := by gcongr
      _ = 8 * 36 ^ m + 34 * 1544 ^ m := by
          rw [mul_assoc 8, ← mul_pow, mul_assoc 34, ← mul_pow]; norm_num
      _ ≤ 42 * 1544 ^ m := by linarith
      _ ≤ 42 ^ m * 1544 ^ m := by gcongr
      _ ≤ ((2 : ℝ) ^ 12) ^ (2 * m) := q5
  have hpos9 : (0 : ℝ) ≤ 9 ^ m := by positivity
  have hpos193 : (0 : ℝ) ≤ 193 ^ m := by positivity
  have htm1 : t ^ m * t = t ^ (m + 1) := by ring
  calc 2 * m * (2 * (2 * m + 2) * (nR * 9 ^ m) + (16 * m / ε + 1) * ((m + 1) * (nR * (193 ^ m * t ^ m))))
      ≤ 2 * m * (2 * (2 * m + 2) * (nR * 9 ^ m) + (17 * m * t) * ((m + 1) * (nR * (193 ^ m * t ^ m)))) := by
        gcongr
    _ = nR * (8 * (m * (m + 1)) * 9 ^ m + 34 * (m * m * (m + 1)) * 193 ^ m * (t ^ m * t)) := by ring
    _ ≤ nR * (8 * (m * (m + 1)) * 9 ^ m * t ^ (2 * m) + 34 * (m * m * (m + 1)) * 193 ^ m * t ^ (2 * m)) := by
        rw [htm1]
        have hX : (0 : ℝ) ≤ 8 * (m * (m + 1)) * 9 ^ m := by positivity
        have hY : (0 : ℝ) ≤ 34 * (m * m * (m + 1)) * 193 ^ m := by positivity
        exact mul_le_mul_of_nonneg_left (add_le_add (le_mul_of_one_le_right hX t1)
          (mul_le_mul_of_nonneg_left t2m hY)) hn
    _ = nR * ((8 * (m * (m + 1)) * 9 ^ m + 34 * (m * m * (m + 1)) * 193 ^ m) * t ^ (2 * m)) := by ring
    _ ≤ nR * (((2 : ℝ) ^ 12) ^ (2 * m) * t ^ (2 * m)) := by gcongr


/-! ## The theorem -/

theorem build_size_main {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) (pts : Fin n → Fin m → ℝ) (r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ¬ Starves pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r) ∧
      (build pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r)).paths.card ≤
        2 * bspFuel n m δ := by
  have hm0 : 0 < m := hm
  have hε0 : 0 < δ / 4 := by positivity
  have hε1 : δ / 4 ≤ 1 := by linarith
  set N : ℝ := (n : ℝ) * (2 ^ 12 / (δ / 4)) ^ (2 * m) with hN
  have hF : bspFuel n m δ = ⌈N⌉₊ + 1 := rfl
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcnt : ∀ f, 2 * m * W pts r (1 + δ / 4) (fun _ _ => 1) f (rootLo hn pts r) (rootHi hn pts r) ≤ N := by
    intro f
    have h1 := root_count_bound hn pts r (δ / 4) hm0 hr hε0 hε1 f
    have h2 : (nCls m (δ / 4) : ℝ) ≤ 16 * m / (δ / 4) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have h3 := final_arith hm0 hε0 hε1 (n : ℝ) (Nat.cast_nonneg _)
    have hB : (0 : ℝ) ≤ (m + 1) * (n * (193 / (δ / 4)) ^ m) := by positivity
    calc 2 * m * W pts r (1 + δ / 4) (fun _ _ => 1) f (rootLo hn pts r) (rootHi hn pts r)
        ≤ 2 * m * (2 * (2 * m + 2) * (n * 9 ^ m) +
            nCls m (δ / 4) * ((m + 1) * (n * (193 / (δ / 4)) ^ m))) := by gcongr
      _ ≤ 2 * m * (2 * (2 * m + 2) * (n * 9 ^ m) +
            (16 * m / (δ / 4) + 1) * ((m + 1) * (n * (193 / (δ / 4)) ^ m))) := by gcongr
      _ ≤ N := h3
  have hW0 : ∀ f, 0 ≤ W pts r (1 + δ / 4) (fun _ _ => 1) f (rootLo hn pts r) (rootHi hn pts r) :=
    fun f => W_nonneg pts r _ _ (fun _ _ => zero_le_one) f _ _
  have hceil : N ≤ ⌈N⌉₊ := Nat.le_ceil N
  refine ⟨fun hs => ?_, ?_⟩
  · have h1 := starves_le_W pts r (1 + δ / 4) hm0 _ _ _ hs
    have h2 := hcnt (bspFuel n m δ)
    have h3 := hW0 (bspFuel n m δ)
    rw [hF] at h1 h2 h3
    push_cast at h1
    nlinarith
  · have h1 := paths_card (build pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r))
    have h2 := leaves_le pts r (1 + δ / 4) hm0 (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r)
    have h3 := hcnt (bspFuel n m δ)
    have h4 : ((build pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r)).paths.card : ℝ)
        ≤ 1 + 2 * ⌈N⌉₊ := by
      have h1' : ((build pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r)
          (rootHi hn pts r)).paths.card : ℝ) + 1 =
          2 * (leaves (build pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r)) : ℝ) := by
        exact_mod_cast h1
      linarith
    have h5 : (build pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r)).paths.card
        ≤ 1 + 2 * ⌈N⌉₊ := by exact_mod_cast h4
    have h6 : 2 * bspFuel n m δ = 2 * ⌈N⌉₊ + 2 := by rw [hF]; ring
    rw [h6]; omega

end DetANN.HPIM.BS

open DetANN.HPIM in
theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) (pts : Fin n → Fin m → ℝ) (r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ¬ Starves pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r) ∧
      (build pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r)).paths.card ≤
        2 * bspFuel n m δ :=
  DetANN.HPIM.BS.build_size_main hm hn pts r δ hr hδ hδ'
