-- Prove2me | solution 1 for GallegoOzerADI.ZeroSetup.J_decreasingDifferences
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T13:22:02.061117+00:00
-- url     : https://prove2.me/submissions/c2a7901f-9fb9-4ce6-b5cf-bc530a2c19f7

import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model
import Definitions.Def_GallegoOzerADI_ZeroSetup_DecreasingDifferences

open MeasureTheory Filter Topology


namespace GallegoOzerADI.ZeroSetup

noncomputable def zs_m (f : ℝ → ℝ) (x : ℝ) : ℝ := ⨅ y : {y : ℝ // x ≤ y}, f y

lemma zs_m_bdd {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (x : ℝ) :
    BddBelow (Set.range fun y : {y : ℝ // x ≤ y} => f y) :=
  ⟨c, by rintro _ ⟨y, rfl⟩; exact hc y⟩

lemma zs_m_le {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {x y : ℝ} (h : x ≤ y) :
    zs_m f x ≤ f y := ciInf_le (zs_m_bdd hc x) ⟨y, h⟩

lemma zs_le_m {f : ℝ → ℝ} {x r : ℝ} (h : ∀ y, x ≤ y → r ≤ f y) : r ≤ zs_m f x := by
  have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_refl x⟩⟩
  exact le_ciInf fun y => h y y.2

lemma zs_m_mono {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) {a b : ℝ} (hab : a ≤ b) :
    zs_m f a ≤ zs_m f b :=
  zs_le_m fun _ hy => zs_m_le hc (hab.trans hy)

lemma zs_m_cont {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (hf : Continuous f) :
    Continuous (zs_m f) := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.1 hf x₀ (ε / 3) (by linarith)
  have key : ∀ a, |a - x₀| < δ → |f a - f x₀| < ε / 3 := fun a ha => by
    have := hδf a (by rwa [Real.dist_eq]); rwa [Real.dist_eq] at this
  refine ⟨δ, hδ, fun x hx => ?_⟩
  rw [Real.dist_eq] at hx ⊢
  have hx' := abs_lt.1 hx
  rcases le_total x₀ x with h | h
  · have h1 := zs_m_mono hc h
    have hfx := abs_lt.1 (key x hx)
    have hmx := zs_m_le hc (le_refl x)
    have h2 : zs_m f x - 2 * ε / 3 ≤ zs_m f x₀ := zs_le_m fun y hy => by
      rcases le_total x y with h' | h'
      · have := zs_m_le hc h'; linarith
      · have := abs_lt.1 (key y (abs_lt.2 ⟨by linarith, by linarith⟩))
        linarith [this.1, this.2, hfx.1, hfx.2]
    rw [abs_lt]; constructor <;> linarith
  · have h1 := zs_m_mono hc h
    have hmx0 := zs_m_le hc (le_refl x₀)
    have h2 : zs_m f x₀ - ε / 3 ≤ zs_m f x := zs_le_m fun y hy => by
      rcases le_total x₀ y with h' | h'
      · have := zs_m_le hc h'; linarith
      · have := abs_lt.1 (key y (abs_lt.2 ⟨by linarith, by linarith⟩))
        linarith [this.1, this.2]
    rw [abs_lt]; constructor <;> linarith

lemma zs_m_rat {f : ℝ → ℝ} {c : ℝ} (hc : ∀ y, c ≤ f y) (hf : Continuous f) (x : ℝ) :
    zs_m f x = ⨅ q : ℚ, f (x + |(q : ℝ)|) := by
  have hbdd : BddBelow (Set.range fun q : ℚ => f (x + |(q : ℝ)|)) :=
    ⟨c, by rintro _ ⟨q, rfl⟩; exact hc _⟩
  apply le_antisymm
  · exact le_ciInf fun q => zs_m_le hc (by linarith [abs_nonneg (q : ℝ)])
  · refine zs_le_m fun y hy => ?_
    have hp : ∀ u : ℝ, (⨅ q : ℚ, f (x + |(q : ℝ)|)) ≤ f (x + |u|) := by
      intro u
      refine Rat.denseRange_cast.induction_on (p := fun u : ℝ => (⨅ q : ℚ, f (x + |(q : ℝ)|)) ≤
        f (x + |u|)) u ?_ (fun q => ciInf_le hbdd q)
      exact isClosed_le continuous_const (hf.comp (continuous_const.add continuous_abs))
    have e : x + |y - x| = y := by rw [abs_of_nonneg (by linarith)]; ring
    have := hp (y - x)
    rwa [e] at this

/-! ### Norm bounds for the transitions -/

/-! ### Convex one-dimensional facts -/

lemma zs_mono_right {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {y : ℝ} (hy : ∀ x, f y ≤ f x)
    {a b : ℝ} (hya : y ≤ a) (hab : a ≤ b) : f a ≤ f b := by
  rcases eq_or_lt_of_le (hya.trans hab) with h | h
  · have : a = b := by linarith
    rw [this]
  · have hd : 0 < b - y := by linarith
    have hθ0 : 0 ≤ (b - a) / (b - y) := div_nonneg (by linarith) hd.le
    have hθ1 : 0 ≤ (a - y) / (b - y) := div_nonneg (by linarith) hd.le
    have hsum : (b - a) / (b - y) + (a - y) / (b - y) = 1 := by
      rw [← add_div, div_eq_one_iff_eq hd.ne']; ring
    have hpt : (b - a) / (b - y) * y + (a - y) / (b - y) * b = a := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd.ne']; ring
    have h1 := hf.2 (Set.mem_univ y) (Set.mem_univ b) hθ0 hθ1 hsum
    simp only [smul_eq_mul] at h1
    rw [hpt] at h1
    have h2 := mul_le_mul_of_nonneg_left (hy b) hθ0
    have h3 : (b - a) / (b - y) * f b + (a - y) / (b - y) * f b = f b := by
      rw [← add_mul, hsum, one_mul]
    linarith

lemma zs_exists_least {f : ℝ → ℝ} (hc : Continuous f) (hco : Tendsto f (cocompact ℝ) atTop) :
    ∃ y, IsLeastMinimizer f y := by
  obtain ⟨y0, hy0⟩ := hc.exists_forall_le hco
  have hcl : IsClosed {z : ℝ | ∀ x, f z ≤ f x} := by
    have : {z : ℝ | ∀ x, f z ≤ f x} = ⋂ x, {z | f z ≤ f x} := by ext z; simp
    rw [this]; exact isClosed_iInter fun x => isClosed_le hc continuous_const
  have hne : ({z : ℝ | ∀ x, f z ≤ f x}).Nonempty := ⟨y0, hy0⟩
  have hev := hco.eventually (eventually_gt_atTop (f y0))
  rw [Filter.Eventually, Filter.mem_cocompact] at hev
  obtain ⟨K, hK, hKsub⟩ := hev
  have hbdd : BddBelow {z : ℝ | ∀ x, f z ≤ f x} := by
    obtain ⟨b, hb⟩ := hK.isBounded.bddBelow
    refine ⟨b, fun z hz => hb ?_⟩
    by_contra hzK
    have h1 : f y0 < f z := hKsub hzK
    have h2 : f z ≤ f y0 := hz y0
    linarith
  exact ⟨sInf _, hcl.csInf_mem hne hbdd, fun z hz => csInf_le hbdd hz⟩

lemma zs_M_eq {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {y : ℝ} (hy : IsLeastMinimizer f y)
    (x : ℝ) : zs_m f x = f (max y x) := by
  have hmin : ∀ z, f y ≤ f z := hy.1
  apply le_antisymm
  · exact zs_m_le hmin (le_max_right _ _)
  · refine zs_le_m fun z hz => ?_
    rcases le_total x y with h | h
    · rw [max_eq_left h]; exact hmin z
    · rw [max_eq_right h]; exact zs_mono_right hf hmin h hz

lemma zs_max_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {y : ℝ} (hmin : ∀ z, f y ≤ f z) :
    ConvexOn ℝ Set.univ (fun x => f (max y x)) := by
  refine ⟨convex_univ, fun a _ b _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  have h1 : y ≤ max y (p * a + q * b) := le_max_left _ _
  have ha1 := mul_le_mul_of_nonneg_left (le_max_left y a) hp
  have ha2 := mul_le_mul_of_nonneg_left (le_max_right y a) hp
  have hb1 := mul_le_mul_of_nonneg_left (le_max_left y b) hq
  have hb2 := mul_le_mul_of_nonneg_left (le_max_right y b) hq
  have h2 : max y (p * a + q * b) ≤ p * max y a + q * max y b := by
    apply max_le
    · have : y = p * y + q * y := by rw [← add_mul, hpq, one_mul]
      linarith
    · linarith
  have h3 := zs_mono_right hf hmin h1 h2
  have h4 := hf.2 (Set.mem_univ (max y a)) (Set.mem_univ (max y b)) hp hq hpq
  simp only [smul_eq_mul] at h4
  linarith

lemma zs_convex_shift {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {a1 a2 δ : ℝ} (h : a2 ≤ a1)
    (hδ : 0 ≤ δ) : f a1 - f a2 ≤ f (a1 + δ) - f (a2 + δ) := by
  rcases eq_or_lt_of_le (add_nonneg (sub_nonneg.2 h) hδ) with h0 | hd
  · have e1 : a1 = a2 := by linarith
    have e2 : δ = 0 := by linarith
    rw [e1, e2]; simp
  · have hl0 : 0 ≤ δ / (a1 - a2 + δ) := div_nonneg hδ hd.le
    have hm0 : 0 ≤ (a1 - a2) / (a1 - a2 + δ) := div_nonneg (sub_nonneg.2 h) hd.le
    have hs : δ / (a1 - a2 + δ) + (a1 - a2) / (a1 - a2 + δ) = 1 := by
      rw [← add_div, div_eq_one_iff_eq hd.ne']; ring
    have hs' : (a1 - a2) / (a1 - a2 + δ) + δ / (a1 - a2 + δ) = 1 := by linarith
    have c1 := hf.2 (Set.mem_univ a2) (Set.mem_univ (a1 + δ)) hl0 hm0 hs
    have c2 := hf.2 (Set.mem_univ a2) (Set.mem_univ (a1 + δ)) hm0 hl0 hs'
    have e1 : δ / (a1 - a2 + δ) * a2 + (a1 - a2) / (a1 - a2 + δ) * (a1 + δ) = a1 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd.ne']; ring
    have e2 : (a1 - a2) / (a1 - a2 + δ) * a2 + δ / (a1 - a2 + δ) * (a1 + δ) = a2 + δ := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd.ne']; ring
    simp only [smul_eq_mul] at c1 c2
    rw [e1] at c1
    rw [e2] at c2
    generalize δ / (a1 - a2 + δ) = l at *
    generalize (a1 - a2) / (a1 - a2 + δ) = m at *
    have hm : m = 1 - l := by linarith
    subst hm
    nlinarith

/-! ### Decreasing differences -/

lemma zs_DD_mono {M : ℕ} {V : ℝ → (Fin M → ℝ) → ℝ} (hDD : DecreasingDifferences V)
    {o o' : Fin M → ℝ} {y y' : ℝ} (hoo : o ≤ o') (hy : IsLeastMinimizer (fun z => V z o) y)
    (hy' : IsLeastMinimizer (fun z => V z o') y') : y ≤ y' := by
  by_contra hlt
  push Not at hlt
  have hmin : ∀ x, V y o ≤ V x o := hy.1
  have hmin' : ∀ x, V y' o' ≤ V x o' := hy'.1
  have h1 := hDD y y' o' o hlt.le hoo
  have h2 := hmin' y
  have h3 := hmin y'
  have h4 : V y o < V y' o := by
    rcases lt_or_eq_of_le h3 with h | h
    · exact h
    · exfalso
      have hmem : ∀ x, V y' o ≤ V x o := fun x => by rw [← h]; exact hmin x
      have := hy.2 hmem
      linarith
  linarith

lemma zs_J_DD {M : ℕ} {V : ℝ → (Fin M → ℝ) → ℝ} (hconv : ∀ o, ConvexOn ℝ Set.univ (fun x => V x o))
    (hDD : DecreasingDifferences V) (ym : (Fin M → ℝ) → ℝ)
    (hym : ∀ o, IsLeastMinimizer (fun z => V z o) (ym o)) :
    DecreasingDifferences (fun x o => V (max (ym o) x) o) := by
  intro x1 x2 θ θ' h12 hθ
  have hyy : ym θ' ≤ ym θ := zs_DD_mono hDD hθ (hym θ') (hym θ)
  have mono' : ∀ a b, a ≤ b → V (max (ym θ') a) θ' ≤ V (max (ym θ') b) θ' := fun a b hab =>
    zs_mono_right (f := fun x => V x θ') (hconv θ') (hym θ').1 (le_max_left _ _)
      (max_le_max le_rfl hab)
  simp only
  rcases le_total (ym θ) x2 with h2 | h2
  · rw [max_eq_right h2, max_eq_right (h2.trans h12), max_eq_right (hyy.trans h2),
      max_eq_right ((hyy.trans h2).trans h12)]
    exact hDD x1 x2 θ θ' h12 hθ
  · rcases le_total x1 (ym θ) with h1 | h1
    · rw [max_eq_left h1, max_eq_left h2]
      have := mono' x2 x1 h12; linarith
    · rw [max_eq_right h1, max_eq_left h2]
      have d := hDD x1 (ym θ) θ θ' h1 hθ
      have m := mono' x2 (ym θ) h2
      rw [max_eq_right hyy] at m
      rw [max_eq_right (hyy.trans h1)]
      linarith

/-! ### Norm bounds for the transitions -/

def zs_n1 {n : ℕ} (o : Fin n → ℝ) : ℝ := ∑ j, |o j|

lemma zs_n1_nonneg {n : ℕ} (o : Fin n → ℝ) : 0 ≤ zs_n1 o :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma zs_le_n1 {n : ℕ} (o : Fin n → ℝ) (j : Fin n) : |o j| ≤ zs_n1 o :=
  Finset.single_le_sum (f := fun j => |o j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

noncomputable def zs_o0 {M : ℕ} (o : Fin M → ℝ) : ℝ := if h : 0 < M then o ⟨0, h⟩ else 0

noncomputable def zs_on {M : ℕ} (o : Fin M → ℝ) (j : Fin M) : ℝ :=
  if h : j.val + 1 < M then o ⟨j.val + 1, h⟩ else 0

lemma zs_nextInv_eq {L M : ℕ} (y : ℝ) (o : Fin M → ℝ) (D : DemandVec L M) :
    nextInv y o D = y - ∑ k : Fin (L + 2), D (Fin.castAdd M k) - zs_o0 o := rfl

lemma zs_nextObs_eq {L M : ℕ} (o : Fin M → ℝ) (D : DemandVec L M) (j : Fin M) :
    nextObs o D j = zs_on o j + D (Fin.natAdd (L + 2) j) := rfl

lemma zs_o0_le {M : ℕ} (o : Fin M → ℝ) : |zs_o0 o| ≤ zs_n1 o := by
  unfold zs_o0; split_ifs with h
  · exact zs_le_n1 o _
  · simpa using zs_n1_nonneg o

lemma zs_on_le {M : ℕ} (o : Fin M → ℝ) (j : Fin M) : |zs_on o j| ≤ zs_n1 o := by
  unfold zs_on; split_ifs with h
  · exact zs_le_n1 o _
  · simpa using zs_n1_nonneg o

lemma zs_o0_mono {M : ℕ} {o o' : Fin M → ℝ} (h : o' ≤ o) : zs_o0 o' ≤ zs_o0 o := by
  unfold zs_o0; split_ifs
  · exact h _
  · exact le_refl _

lemma zs_o0_nonneg {M : ℕ} {o : Fin M → ℝ} (h : 0 ≤ o) : 0 ≤ zs_o0 o := by
  unfold zs_o0; split_ifs
  · exact h _
  · exact le_refl _

lemma zs_nextObs_mono {L M : ℕ} {o o' : Fin M → ℝ} (h : o' ≤ o) (D : DemandVec L M) :
    nextObs o' D ≤ nextObs o D := by
  intro j
  rw [zs_nextObs_eq, zs_nextObs_eq]
  unfold zs_on; split_ifs
  · linarith [h ⟨j.val + 1, by assumption⟩]
  · exact le_refl _

lemma zs_nextObs_nonneg {L M : ℕ} {o : Fin M → ℝ} (h : 0 ≤ o) {D : DemandVec L M}
    (hD : ∀ k, 0 ≤ D k) : 0 ≤ nextObs o D := by
  intro j
  rw [zs_nextObs_eq]
  unfold zs_on; split_ifs
  · exact add_nonneg (h _) (hD _)
  · simpa using hD _

lemma zs_o0_cont {M : ℕ} : Continuous (fun o : Fin M → ℝ => zs_o0 o) := by
  by_cases h : 0 < M
  · simp only [zs_o0, dif_pos h]; exact continuous_apply _
  · simp only [zs_o0, dif_neg h]; exact continuous_const

lemma zs_on_cont {M : ℕ} (j : Fin M) : Continuous (fun o : Fin M → ℝ => zs_on o j) := by
  by_cases h : j.val + 1 < M
  · simp only [zs_on, dif_pos h]; exact continuous_apply _
  · simp only [zs_on, dif_neg h]; exact continuous_const

lemma zs_nextInv_le {L M : ℕ} (y : ℝ) (o : Fin M → ℝ) (D : DemandVec L M) :
    |nextInv y o D| ≤ |y| + (L + 2) * zs_n1 D + zs_n1 o := by
  rw [zs_nextInv_eq]
  have h1 : |∑ k : Fin (L + 2), D (Fin.castAdd M k)| ≤ (L + 2) * zs_n1 D := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => zs_le_n1 D _).trans ?_
    simp
  have h2 := zs_o0_le o
  have h3 := abs_sub (y - ∑ k : Fin (L + 2), D (Fin.castAdd M k)) (zs_o0 o)
  have h4 := abs_sub y (∑ k : Fin (L + 2), D (Fin.castAdd M k))
  linarith

lemma zs_nextObs_le {L M : ℕ} (o : Fin M → ℝ) (D : DemandVec L M) :
    zs_n1 (nextObs o D) ≤ M * (zs_n1 o + zs_n1 D) := by
  have : ∀ j : Fin M, |nextObs o D j| ≤ zs_n1 o + zs_n1 D := fun j => by
    rw [zs_nextObs_eq]
    exact (abs_add_le _ _).trans (add_le_add (zs_on_le o _) (zs_le_n1 D _))
  calc zs_n1 (nextObs o D) = ∑ j, |nextObs o D j| := rfl
    _ ≤ ∑ _j : Fin M, (zs_n1 o + zs_n1 D) := Finset.sum_le_sum fun j _ => this j
    _ = _ := by simp [mul_add]

lemma zs_trans_le {L M : ℕ} (y : ℝ) (o : Fin M → ℝ) (D : DemandVec L M) :
    |nextInv y o D| + zs_n1 (nextObs o D) ≤
      |y| + (L + M + 2) * zs_n1 D + (M + 1) * zs_n1 o := by
  have := zs_nextInv_le y o D
  have := zs_nextObs_le o D
  linarith

/-! ### The backward induction -/

variable {L M : ℕ}

def zsInv (f : ℝ → (Fin M → ℝ) → ℝ) : Prop :=
  (∀ o, Continuous (fun x => f x o)) ∧
  Measurable (fun p : ℝ × (Fin M → ℝ) => f p.1 p.2) ∧
  (∃ c, ∀ x o, c ≤ f x o) ∧
  (∃ C B, 0 ≤ B ∧ ∀ x o, f x o ≤ C + B * (|x| + zs_n1 o)) ∧
  (∀ o, ConvexOn ℝ Set.univ (fun x => f x o)) ∧
  DecreasingDifferences f

lemma zs_VJ {V : ℝ → (Fin M → ℝ) → ℝ} (h : zsInv V)
    (hco : ∀ o, Tendsto (fun y => V y o) (cocompact ℝ) atTop) :
    zsInv (fun x o => zs_m (fun y => V y o) x) := by
  obtain ⟨hcont, hmeas, ⟨c, hc⟩, ⟨C, B, hB, hCB⟩, hconv, hDD⟩ := h
  have hym : ∀ o, ∃ y, IsLeastMinimizer (fun z => V z o) y := fun o =>
    zs_exists_least (hcont o) (hco o)
  choose ym hym using hym
  have hrep : ∀ x o, zs_m (fun y => V y o) x = V (max (ym o) x) o := fun x o =>
    zs_M_eq (f := fun y => V y o) (hconv o) (hym o) x
  refine ⟨fun o => zs_m_cont (hc · o) (hcont o), ?_, ⟨c, fun x o => zs_le_m fun y _ => hc y o⟩,
    ⟨C, B, hB, fun x o => (zs_m_le (hc · o) (le_refl x)).trans (hCB x o)⟩, fun o => ?_, ?_⟩
  · have : (fun p : ℝ × (Fin M → ℝ) => zs_m (fun y => V y p.2) p.1) =
        fun p => ⨅ q : ℚ, V (p.1 + |(q : ℝ)|) p.2 := funext fun p => by
      rw [zs_m_rat (hc · p.2) (hcont p.2) p.1]
    rw [this]
    refine Measurable.iInf fun q => ?_
    exact hmeas.comp ((measurable_fst.add_const _).prodMk measurable_snd)
  · have : (fun x => zs_m (fun y => V y o) x) = fun x => V (max (ym o) x) o :=
      funext fun x => hrep x o
    rw [this]
    exact zs_max_convex (f := fun y => V y o) (hconv o) (hym o).1
  · have : (fun x o => zs_m (fun y => V y o) x) = fun x o => V (max (ym o) x) o :=
      funext fun x => funext fun o => hrep x o
    rw [this]
    exact zs_J_DD hconv hDD ym hym

lemma zs_base (P : Model L M) : zsInv (P.J (P.T + 1)) := by
  have h0 : P.J (P.T + 1) = fun _ _ => 0 :=
    funext fun x => funext fun o => P.J_of_lt (by omega) x o
  rw [h0]
  refine ⟨fun _ => continuous_const, measurable_const, ⟨0, fun _ _ => le_refl _⟩,
    ⟨0, 0, le_refl _, fun x o => by simp⟩, fun o => convexOn_const 0 convex_univ, ?_⟩
  intro x1 x2 θ θ' _ _
  simp

lemma zs_JV (P : Model L M) (hP : P.Assumptions) (s : ℕ) (hs1 : 1 ≤ s) (hsT : s ≤ P.T)
    (h : zsInv (P.J (s + 1))) :
    zsInv (P.V s) ∧ ∀ o, Tendsto (fun y => P.V s y o) (cocompact ℝ) atTop := by
  obtain ⟨hcont, hmeas, ⟨c, hc⟩, ⟨C, B, hB, hCB⟩, hconv, hDD⟩ := h
  have := hP.prob s hs1 hsT
  have hαpos : 0 < P.α (s + 1) := hP.discount_pos s hs1 hsT
  have hGc : Continuous (P.G s) :=
    continuousOn_univ.1 ((hP.convex s hs1 hsT).continuousOn isOpen_univ)
  obtain ⟨y₀, hy₀⟩ := hGc.exists_forall_le (hP.coercive s hs1 hsT)
  obtain ⟨a, b, hab⟩ := hP.linear_growth s hs1 hsT
  have hDint : Integrable (fun D : DemandVec L M => zs_n1 D) (P.μ s) := by
    unfold zs_n1
    exact integrable_finsetSum _ fun k _ => (hP.demand_integrable s hs1 hsT k).abs
  have hXc : Continuous (fun q : (ℝ × (Fin M → ℝ)) × DemandVec L M =>
      nextInv q.1.1 q.1.2 q.2) := by
    simp only [zs_nextInv_eq]
    refine (continuous_fst.fst.sub ?_).sub (zs_o0_cont.comp continuous_fst.snd)
    exact continuous_finsetSum _ fun k _ => (continuous_apply _).comp continuous_snd
  have hOc : Continuous (fun q : (ℝ × (Fin M → ℝ)) × DemandVec L M =>
      nextObs q.1.2 q.2) := by
    refine continuous_pi fun j => ?_
    simp only [zs_nextObs_eq]
    exact ((zs_on_cont j).comp continuous_fst.snd).add
      ((continuous_apply _).comp continuous_snd)
  have hΦ : Measurable (fun q : (ℝ × (Fin M → ℝ)) × DemandVec L M =>
      ((nextInv q.1.1 q.1.2 q.2, nextObs q.1.2 q.2) : ℝ × (Fin M → ℝ))) :=
    (hXc.prodMk hOc).measurable
  have hFmeas2 : Measurable (fun q : (ℝ × (Fin M → ℝ)) × DemandVec L M =>
      P.J (s + 1) (nextInv q.1.1 q.1.2 q.2) (nextObs q.1.2 q.2)) := hmeas.comp hΦ
  have hFmeas : ∀ y o, Measurable (fun D => P.J (s + 1) (nextInv y o D) (nextObs o D)) :=
    fun y o => hFmeas2.comp (measurable_prodMk_left (x := ((y, o) : ℝ × (Fin M → ℝ))))
  have hFup : ∀ (y : ℝ) (o : Fin M → ℝ) (D : DemandVec L M),
      P.J (s + 1) (nextInv y o D) (nextObs o D) ≤
      C + B * (|y| + (L + M + 2) * zs_n1 D + (M + 1) * zs_n1 o) := fun y o D => by
    have h1 := hCB (nextInv y o D) (nextObs o D)
    have h2 := zs_trans_le y o D
    have h3 := mul_le_mul_of_nonneg_left h2 hB
    linarith
  have hstuff : ∀ (y : ℝ) (o : Fin M → ℝ) (D : DemandVec L M),
      0 ≤ B * (|y| + (L + M + 2) * zs_n1 D + (M + 1) * zs_n1 o) := fun y o D =>
    mul_nonneg hB (add_nonneg (add_nonneg (abs_nonneg y)
      (mul_nonneg (by positivity) (zs_n1_nonneg D)))
      (mul_nonneg (by positivity) (zs_n1_nonneg o)))
  have hFbd : ∀ (y : ℝ) (o : Fin M → ℝ) (D : DemandVec L M),
      |P.J (s + 1) (nextInv y o D) (nextObs o D)| ≤
      |c| + |C| + B * (|y| + (L + M + 2) * zs_n1 D + (M + 1) * zs_n1 o) :=
    fun y o D => by
    have h1 := hFup y o D
    have h2 := hc (nextInv y o D) (nextObs o D)
    have h3 := hstuff y o D
    rw [abs_le]
    constructor
    · linarith [neg_abs_le c, abs_nonneg C]
    · linarith [le_abs_self C, abs_nonneg c]
  have hFint : ∀ y o, Integrable (fun D => P.J (s + 1) (nextInv y o D) (nextObs o D)) (P.μ s) :=
    fun y o => by
    refine Integrable.mono' ((integrable_const
      (|c| + |C| + B * (|y| + (M + 1) * zs_n1 o))).add
      (hDint.const_mul (B * (L + M + 2)))) (hFmeas y o).aestronglyMeasurable
      (Filter.Eventually.of_forall fun D => ?_)
    rw [Real.norm_eq_abs]
    have := hFbd y o D
    simp only [Pi.add_apply]
    linarith
  have hIlow : ∀ y o, c ≤ ∫ D, P.J (s + 1) (nextInv y o D) (nextObs o D) ∂(P.μ s) := fun y o => by
    have := integral_mono (integrable_const c) (hFint y o) (fun D => hc _ _)
    simpa using this
  have hIup : ∀ y o, ∫ D, P.J (s + 1) (nextInv y o D) (nextObs o D) ∂(P.μ s) ≤
      C + B * (|y| + (M + 1) * zs_n1 o) +
        B * (L + M + 2) * ∫ D, zs_n1 D ∂(P.μ s) := fun y o => by
    have hg : Integrable (fun D => (C + B * (|y| + (M + 1) * zs_n1 o)) +
        B * (L + M + 2) * zs_n1 D) (P.μ s) :=
      (integrable_const _).add (hDint.const_mul _)
    have hpt : ∀ D : DemandVec L M, P.J (s + 1) (nextInv y o D) (nextObs o D) ≤
        (C + B * (|y| + (M + 1) * zs_n1 o)) + B * (L + M + 2) * zs_n1 D :=
      fun D => by have := hFup y o D; linarith
    have := integral_mono (hFint y o) hg hpt
    rw [integral_add (integrable_const _) (hDint.const_mul _), integral_const_mul] at this
    simpa using this
  have hVlow : ∀ y o, P.G s y₀ + P.α (s + 1) * c ≤ P.V s y o := fun y o => by
    have := mul_le_mul_of_nonneg_left (hIlow y o) hαpos.le
    have := hy₀ y
    show _ ≤ P.G s y + P.α (s + 1) * _
    linarith
  refine ⟨⟨fun o => ?_, ?_, ⟨_, hVlow⟩, ?_, fun o => ?_, ?_⟩, fun o => ?_⟩
  · -- continuity
    show Continuous fun y => P.G s y + P.α (s + 1) *
      ∫ D, P.J (s + 1) (nextInv y o D) (nextObs o D) ∂(P.μ s)
    refine hGc.add (continuous_const.mul ?_)
    rw [continuous_iff_continuousAt]
    intro y₁
    have hbint : Integrable (fun D => (|c| + |C| + B * ((|y₁| + 1) + (M + 1) * zs_n1 o)) +
        B * (L + M + 2) * zs_n1 D) (P.μ s) := (integrable_const _).add (hDint.const_mul _)
    refine continuousAt_of_dominated ?_ ?_ hbint ?_
    · exact Filter.Eventually.of_forall fun y => (hFmeas y o).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds y₁ one_pos] with y hy
      refine Filter.Eventually.of_forall fun D => ?_
      rw [Real.norm_eq_abs]
      have h1 := hFbd y o D
      have h2 : |y| ≤ |y₁| + 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have := abs_sub_abs_le_abs_sub y y₁; linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hB
      linarith
    · refine Filter.Eventually.of_forall fun D => ?_
      have : Continuous fun y => nextInv y o D := by
        simp only [zs_nextInv_eq]; fun_prop
      exact ((hcont (nextObs o D)).comp this).continuousAt
  · -- measurability
    show Measurable fun p : ℝ × (Fin M → ℝ) => P.G s p.1 + P.α (s + 1) *
      ∫ D, P.J (s + 1) (nextInv p.1 p.2 D) (nextObs p.2 D) ∂(P.μ s)
    refine (hGc.measurable.comp measurable_fst).add (measurable_const.mul ?_)
    exact (hFmeas2.stronglyMeasurable.integral_prod_right' (ν := P.μ s)).measurable
  · -- upper bound
    refine ⟨a + P.α (s + 1) * (C + B * (L + M + 2) * ∫ D, zs_n1 D ∂(P.μ s)),
      |b| + P.α (s + 1) * (B * (M + 1)),
      add_nonneg (abs_nonneg b) (mul_nonneg hαpos.le (mul_nonneg hB (by positivity))),
      fun y o => ?_⟩
    have h1 := hIup y o
    have h2 := mul_le_mul_of_nonneg_left h1 hαpos.le
    have h3 : P.G s y ≤ a + |b| * |y| := by
      have := hab y
      have := le_abs_self (P.G s y)
      have := mul_le_mul_of_nonneg_right (le_abs_self b) (abs_nonneg y)
      linarith
    have h4 := zs_n1_nonneg o
    have h5 : P.α (s + 1) * B * |y| ≤ P.α (s + 1) * B * (M + 1) * |y| := by
      have h0 : 0 ≤ P.α (s + 1) * B * |y| := mul_nonneg (mul_nonneg hαpos.le hB) (abs_nonneg y)
      have hM : (0:ℝ) ≤ M := Nat.cast_nonneg M
      nlinarith [mul_nonneg h0 hM]
    have h6 : 0 ≤ |b| * zs_n1 o := mul_nonneg (abs_nonneg b) h4
    show P.G s y + P.α (s + 1) * _ ≤ _
    nlinarith
  · -- convexity
    refine ⟨convex_univ, fun x₁ _ x₂ _ p q hp hq hpq => ?_⟩
    have hGx := (hP.convex s hs1 hsT).2 (Set.mem_univ x₁) (Set.mem_univ x₂) hp hq hpq
    simp only [smul_eq_mul] at hGx ⊢
    have hpt : ∀ D : DemandVec L M, P.J (s + 1) (nextInv (p * x₁ + q * x₂) o D) (nextObs o D) ≤
        p * P.J (s + 1) (nextInv x₁ o D) (nextObs o D) +
          q * P.J (s + 1) (nextInv x₂ o D) (nextObs o D) := fun D => by
      have e : nextInv (p * x₁ + q * x₂) o D = p * nextInv x₁ o D + q * nextInv x₂ o D := by
        simp only [zs_nextInv_eq]
        have : q = 1 - p := by linarith
        subst this; ring
      have := (hconv (nextObs o D)).2 (Set.mem_univ (nextInv x₁ o D))
        (Set.mem_univ (nextInv x₂ o D)) hp hq hpq
      simp only [smul_eq_mul] at this
      rw [e]; exact this
    have i1 : Integrable (fun D => p * P.J (s + 1) (nextInv x₁ o D) (nextObs o D)) (P.μ s) :=
      (hFint x₁ o).const_mul p
    have i3 : Integrable (fun D => q * P.J (s + 1) (nextInv x₂ o D) (nextObs o D)) (P.μ s) :=
      (hFint x₂ o).const_mul q
    have hg : Integrable (fun D => p * P.J (s + 1) (nextInv x₁ o D) (nextObs o D) +
        q * P.J (s + 1) (nextInv x₂ o D) (nextObs o D)) (P.μ s) := i1.add i3
    have hint := integral_mono (hFint _ o) hg hpt
    rw [integral_add i1 i3, integral_const_mul, integral_const_mul] at hint
    show P.G s _ + P.α (s + 1) * _ ≤
      p * (P.G s x₁ + P.α (s + 1) * _) + q * (P.G s x₂ + P.α (s + 1) * _)
    have h1 := mul_le_mul_of_nonneg_left hint hαpos.le
    nlinarith
  · -- decreasing differences
    intro x₁ x₂ θ θ' h12 hθ
    have hpt : ∀ D : DemandVec L M,
        P.J (s + 1) (nextInv x₁ θ D) (nextObs θ D) - P.J (s + 1) (nextInv x₂ θ D) (nextObs θ D) ≤
        P.J (s + 1) (nextInv x₁ θ' D) (nextObs θ' D) -
          P.J (s + 1) (nextInv x₂ θ' D) (nextObs θ' D) := fun D => by
      have hle : nextInv x₂ θ D ≤ nextInv x₁ θ D := by
        simp only [zs_nextInv_eq]; linarith
      have d1 := hDD (nextInv x₁ θ D) (nextInv x₂ θ D) (nextObs θ D) (nextObs θ' D) hle
        (zs_nextObs_mono hθ D)
      have hδ : 0 ≤ zs_o0 θ - zs_o0 θ' := sub_nonneg.2 (zs_o0_mono hθ)
      have d2 := zs_convex_shift (hconv (nextObs θ' D)) hle hδ
      have e1 : nextInv x₁ θ D + (zs_o0 θ - zs_o0 θ') = nextInv x₁ θ' D := by
        simp only [zs_nextInv_eq]; ring
      have e2 : nextInv x₂ θ D + (zs_o0 θ - zs_o0 θ') = nextInv x₂ θ' D := by
        simp only [zs_nextInv_eq]; ring
      rw [e1, e2] at d2
      linarith
    have g1 : Integrable (fun D => P.J (s + 1) (nextInv x₁ θ D) (nextObs θ D) -
        P.J (s + 1) (nextInv x₂ θ D) (nextObs θ D)) (P.μ s) := (hFint x₁ θ).sub (hFint x₂ θ)
    have g2 : Integrable (fun D => P.J (s + 1) (nextInv x₁ θ' D) (nextObs θ' D) -
        P.J (s + 1) (nextInv x₂ θ' D) (nextObs θ' D)) (P.μ s) := (hFint x₁ θ').sub (hFint x₂ θ')
    have hint := integral_mono g1 g2 hpt
    rw [integral_sub (hFint x₁ θ) (hFint x₂ θ), integral_sub (hFint x₁ θ') (hFint x₂ θ')] at hint
    show (P.G s x₁ + P.α (s + 1) * _) - (P.G s x₂ + P.α (s + 1) * _) ≤
      (P.G s x₁ + P.α (s + 1) * _) - (P.G s x₂ + P.α (s + 1) * _)
    have h1 := mul_le_mul_of_nonneg_left hint hαpos.le
    nlinarith
  · -- coercivity
    have hlow : ∀ y, P.G s y + P.α (s + 1) * c ≤ P.V s y o := fun y => by
      have := mul_le_mul_of_nonneg_left (hIlow y o) hαpos.le
      show _ ≤ P.G s y + P.α (s + 1) * _
      linarith
    exact tendsto_atTop_mono hlow (tendsto_atTop_add_const_right _ _ (hP.coercive s hs1 hsT))

lemma zs_all (P : Model L M) (hP : P.Assumptions) : ∀ n, n ≤ P.T →
    zsInv (P.J (P.T + 1 - n)) := by
  intro n
  induction n with
  | zero => intro _; rw [Nat.sub_zero]; exact zs_base P
  | succ n ih =>
    intro hn
    have h := ih (by omega)
    have e1 : P.T + 1 - n = (P.T - n) + 1 := by omega
    rw [e1] at h
    have hV := zs_JV P hP (P.T - n) (by omega) (by omega) h
    have e2 : P.T + 1 - (n + 1) = P.T - n := by omega
    rw [e2]
    have hJ : P.J (P.T - n) = fun x o => zs_m (fun y => P.V (P.T - n) y o) x :=
      funext fun x => funext fun o => P.J_of_le (by omega) x o
    rw [hJ]
    exact zs_VJ hV.1 hV.2

lemma zs_V_inv (P : Model L M) (hP : P.Assumptions) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) :
    zsInv (P.V t) ∧ ∀ o, Tendsto (fun y => P.V t y o) (cocompact ℝ) atTop := by
  have h := zs_all P hP (P.T - t) (by omega)
  have e : P.T + 1 - (P.T - t) = t + 1 := by omega
  rw [e] at h
  exact zs_JV P hP t ht1 htT h

lemma zs_J_inv (P : Model L M) (hP : P.Assumptions) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) :
    zsInv (P.J t) := by
  have h := zs_all P hP (P.T + 1 - t) (by omega)
  have e : P.T + 1 - (P.T + 1 - t) = t := by omega
  rwa [e] at h

lemma zs_rep (P : Model L M) (hP : P.Assumptions) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T)
    (o : Fin M → ℝ) (y : ℝ) (hy : IsLeastMinimizer (fun z => P.V t z o) y) (x : ℝ) :
    P.J t x o = P.V t (max y x) o := by
  rw [P.J_of_le htT]
  exact zs_M_eq (f := fun z => P.V t z o) ((zs_V_inv P hP t ht1 htT).1.2.2.2.2.1 o) hy x

theorem zs_V_convex_coercive_core (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ConvexOn ℝ Set.univ (fun x => P.V t x o) ∧
      Tendsto (fun x => P.V t x o) (cocompact ℝ) atTop :=
  ⟨(zs_V_inv P hP t ht1 htT).1.2.2.2.2.1 o, (zs_V_inv P hP t ht1 htT).2 o⟩

theorem zs_base_stock_optimal_core (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ∃ y : ℝ, IsLeastMinimizer (fun z => P.V t z o) y ∧
      ∀ x : ℝ, P.J t x o = P.V t (max y x) o := by
  obtain ⟨y, hy⟩ := zs_exists_least ((zs_V_inv P hP t ht1 htT).1.1 o) ((zs_V_inv P hP t ht1 htT).2 o)
  exact ⟨y, hy, zs_rep P hP t ht1 htT o y hy⟩

theorem zs_V_DD_core (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) :
    DecreasingDifferences (fun x o => P.V t x o) :=
  (zs_V_inv P hP t ht1 htT).1.2.2.2.2.2

theorem zs_J_DD_core (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) :
    DecreasingDifferences (fun x o => P.J t x o) :=
  (zs_J_inv P hP t ht1 htT).2.2.2.2.2

theorem zs_baseStock_mono_core (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o o' : Fin M → ℝ) (y y' : ℝ)
    (hoo : o ≤ o') (hy : IsLeastMinimizer (fun z => P.V t z o) y)
    (hy' : IsLeastMinimizer (fun z => P.V t z o') y') :
    y ≤ y' :=
  zs_DD_mono (zs_V_inv P hP t ht1 htT).1.2.2.2.2.2 hoo hy hy'
end GallegoOzerADI.ZeroSetup

open GallegoOzerADI.ZeroSetup


theorem solution {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) :
    DecreasingDifferences (fun x o => P.J t x o) := by
  exact zs_J_DD_core P hP t ht1 htT
