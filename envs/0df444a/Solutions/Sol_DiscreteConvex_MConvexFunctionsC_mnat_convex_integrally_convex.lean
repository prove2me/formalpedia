-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsC.mnat_convex_integrally_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:09:47.384923+00:00
-- url     : https://prove2.me/submissions/5ac997fe-8d9b-4700-910b-9f1a12aaa4d9

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsIntegrallyConvexFunction



namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Step 1: the M♮-exchange property extracted from `MNaturalConvex`. -/

def liftVec (a : V → ℤ) : Option V → ℤ := fun o => o.elim (-(∑ v, a v)) (fun v => a v)

lemma liftVec_some (a : V → ℤ) (v : V) : liftVec a (some v) = a v := rfl
lemma liftVec_none (a : V → ℤ) : liftVec a none = -(∑ v, a v) := rfl

lemma lifted_eq_of (f : (V → ℤ) → WithTop ℝ) (x : Option V → ℤ)
    (h : x none = -(∑ v, x (some v))) : LiftedFunction f x = f (fun v => x (some v)) := by
  unfold LiftedFunction; rw [if_pos h]

lemma lifted_liftVec (f : (V → ℤ) → WithTop ℝ) (a : V → ℤ) :
    LiftedFunction f (liftVec a) = f a := by
  rw [lifted_eq_of]
  · rfl
  · rfl

theorem mnat_exc (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) (a b : V → ℤ)
    (ha : f a ≠ ⊤) (hb : f b ≠ ⊤) (u : V) (hu : b u < a u) :
    ∃ d : V → ℤ, d u = 1 ∧ (∀ w, d w = 0 ∨ (d w = 1 ∧ b w < a w) ∨ (d w = -1 ∧ a w < b w)) ∧
      f (fun w => a w - d w) + f (fun w => b w + d w) ≤ f a + f b := by
  have hA : liftVec a ∈ DomZ (LiftedFunction f) := by
    show LiftedFunction f (liftVec a) ≠ ⊤
    rw [lifted_liftVec]; exact ha
  have hB : liftVec b ∈ DomZ (LiftedFunction f) := by
    show LiftedFunction f (liftVec b) ≠ ⊤
    rw [lifted_liftVec]; exact hb
  have hU : some u ∈ SuppPos (liftVec a) (liftVec b) := by
    simp [SuppPos, liftVec_some, hu]
  obtain ⟨v, hv, hineq⟩ := hf _ hA _ hB _ hU
  rw [lifted_liftVec, lifted_liftVec] at hineq
  simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases v with _ | v
  · refine ⟨CharVec u, by simp [CharVec], ?_, ?_⟩
    · intro w; unfold CharVec; split_ifs with h
      · right; left; exact ⟨rfl, h ▸ hu⟩
      · left; rfl
    · have e1 : LiftedFunction f (fun w => liftVec a w - CharVec (some u) w + CharVec none w)
          = f (fun w => a w - CharVec u w) := by
        rw [lifted_eq_of]
        · congr 1; funext w; simp [liftVec, CharVec]
        · simp [liftVec, CharVec, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq'] <;> ring
      have e2 : LiftedFunction f (fun w => liftVec b w + CharVec (some u) w - CharVec none w)
          = f (fun w => b w + CharVec u w) := by
        rw [lifted_eq_of]
        · congr 1; funext w; simp [liftVec, CharVec]
        · simp [liftVec, CharVec, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq'] <;> ring
      rw [e1, e2] at hineq
      exact hineq
  · simp only [liftVec_some] at hv
    have huv : u ≠ v := by intro h; subst h; omega
    refine ⟨fun w => CharVec u w - CharVec v w, by simp [CharVec, huv, huv.symm], ?_, ?_⟩
    · intro w; simp only [CharVec]; split_ifs with h1 h2 h2
      · exact absurd (h1.symm.trans h2) huv
      · right; left; exact ⟨by norm_num, h1 ▸ hu⟩
      · right; right; exact ⟨by norm_num, h2 ▸ hv⟩
      · left; norm_num
    · have e1 : LiftedFunction f (fun w => liftVec a w - CharVec (some u) w + CharVec (some v) w)
          = f (fun w => a w - (CharVec u w - CharVec v w)) := by
        rw [lifted_eq_of]
        · congr 1; funext w; simp [liftVec, CharVec]; ring
        · simp [liftVec, CharVec, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq'] <;> ring
      have e2 : LiftedFunction f (fun w => liftVec b w + CharVec (some u) w - CharVec (some v) w)
          = f (fun w => b w + (CharVec u w - CharVec v w)) := by
        rw [lifted_eq_of]
        · congr 1; funext w; simp [liftVec, CharVec]; ring
        · simp [liftVec, CharVec, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq'] <;> ring
      rw [e1, e2] at hineq
      exact hineq

/-! ### Step 2: generic helper lemmas. -/

lemma avg_lemma {ι : Type*} [Fintype ι] (μ c : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hsum : ∑ i, μ i * c i = 0) (i0 : ι) (h0 : 0 < μ i0) (hc : 0 < c i0) :
    ∃ j, 0 < μ j ∧ c j < 0 := by
  by_contra hcon
  push_neg at hcon
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ μ j * c j := by
    intro j _
    rcases (hμ j).lt_or_eq with h | h
    · exact mul_nonneg (hμ j) (hcon j h)
    · rw [← h]; simp
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i0 (Finset.mem_univ _)
  have h2 : 0 < μ i0 * c i0 := mul_pos h0 hc
  linarith

lemma sum_shift {ι : Type*} [Fintype ι] [DecidableEq ι] (μ g : ι → ℝ) (m : ℝ) (a b a' b' : ι) :
    ∑ i, (μ i + m * ((if i = a' then (1:ℝ) else 0) + (if i = b' then 1 else 0)
      - (if i = a then 1 else 0) - (if i = b then 1 else 0))) * g i
      = ∑ i, μ i * g i + m * (g a' + g b' - g a - g b) := by
  have : ∀ i, (μ i + m * ((if i = a' then (1:ℝ) else 0) + (if i = b' then 1 else 0)
      - (if i = a then 1 else 0) - (if i = b then 1 else 0))) * g i
      = μ i * g i + m * ((if i = a' then g i else 0) + (if i = b' then g i else 0)
      - (if i = a then g i else 0) - (if i = b then g i else 0)) := by
    intro i; split_ifs <;> ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma phi_diff (a b d : V → ℤ) (p : V → ℝ) :
    (∑ w, (((a w - d w : ℤ) : ℝ) - p w) ^ 2) + (∑ w, (((b w + d w : ℤ) : ℝ) - p w) ^ 2)
      - (∑ w, ((a w : ℝ) - p w) ^ 2) - (∑ w, ((b w : ℝ) - p w) ^ 2)
      = ∑ w, 2 * (d w : ℝ) * (((b w : ℝ) - a w) + d w) := by
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro w _; push_cast; ring

lemma phi_diff_neg (a b d : V → ℤ) (p : V → ℝ) (u : V) (hdu : d u = 1)
    (hdw : ∀ w, d w = 0 ∨ (d w = 1 ∧ b w < a w) ∨ (d w = -1 ∧ a w < b w))
    (hab : b u + 2 ≤ a u) :
    ∑ w, 2 * (d w : ℝ) * (((b w : ℝ) - a w) + d w) ≤ -2 := by
  set t : V → ℝ := fun w => 2 * (d w : ℝ) * (((b w : ℝ) - a w) + d w) with ht
  have hnonpos : ∀ w, t w ≤ 0 := by
    intro w
    simp only [ht]
    rcases hdw w with h | ⟨h, h'⟩ | ⟨h, h'⟩
    · simp [h]
    · have h1 : (d w : ℝ) = 1 := by exact_mod_cast h
      have h2 : (b w : ℝ) + 1 ≤ a w := by exact_mod_cast h'
      rw [h1]; nlinarith
    · have h1 : (d w : ℝ) = -1 := by exact_mod_cast h
      have h2 : (a w : ℝ) + 1 ≤ b w := by exact_mod_cast h'
      rw [h1]; nlinarith
  have htu : t u ≤ -2 := by
    simp only [ht]
    have h1 : (d u : ℝ) = 1 := by exact_mod_cast hdu
    have h2 : (b u : ℝ) + 2 ≤ a u := by exact_mod_cast hab
    rw [h1]; nlinarith
  have := Finset.add_sum_erase Finset.univ t (Finset.mem_univ u)
  have h3 : ∑ w ∈ Finset.univ.erase u, t w ≤ 0 := Finset.sum_nonpos (fun w _ => hnonpos w)
  show ∑ w, t w ≤ -2
  linarith

/-! ### Step 3: the box and the compact feasible set. -/

noncomputable def boxOf (S : Finset (V → ℤ)) : Finset (V → ℤ) :=
  Fintype.piFinset (fun v => Finset.Icc (-(∑ z ∈ S, |z v|)) (∑ z ∈ S, |z v|))

lemma mem_boxOf {S : Finset (V → ℤ)} {y : V → ℤ} :
    y ∈ boxOf S ↔ ∀ v, -(∑ z ∈ S, |z v|) ≤ y v ∧ y v ≤ ∑ z ∈ S, |z v| := by
  simp [boxOf, Fintype.mem_piFinset, Finset.mem_Icc]

lemma subset_boxOf (S : Finset (V → ℤ)) : S ⊆ boxOf S := by
  intro y hy
  rw [mem_boxOf]
  intro v
  have h1 : |y v| ≤ ∑ z ∈ S, |z v| := Finset.single_le_sum (fun z _ => abs_nonneg (z v)) hy
  constructor
  · linarith [neg_abs_le (y v)]
  · linarith [le_abs_self (y v)]

lemma boxOf_closed (S : Finset (V → ℤ)) (y y' z : V → ℤ) (hy : y ∈ boxOf S) (hy' : y' ∈ boxOf S)
    (hz : ∀ v, (y v ≤ z v ∨ y' v ≤ z v) ∧ (z v ≤ y v ∨ z v ≤ y' v)) : z ∈ boxOf S := by
  rw [mem_boxOf] at *
  intro v
  have h1 := hy v
  have h2 := hy' v
  have h3 := hz v
  constructor <;> omega

section Main

variable (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (B : Finset (V → ℤ))

def Feas : Set (↥B → ℝ) :=
  {μ | (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i = 1) ∧ (∀ w, ∑ i, μ i * ((i.1 w : ℤ) : ℝ) = p w) ∧
    (∀ i, f i.1 = ⊤ → μ i = 0)}

def Val (μ : ↥B → ℝ) : ℝ := ∑ i, μ i * (f i.1).untopD 0

def Phi (μ : ↥B → ℝ) : ℝ := ∑ i, μ i * ∑ w, (((i.1 w : ℤ) : ℝ) - p w) ^ 2

lemma val_continuous : Continuous (Val f B) := by
  unfold Val; fun_prop

lemma phi_continuous : Continuous (Phi p B) := by
  unfold Phi; fun_prop

lemma feas_closed : IsClosed (Feas f p B) := by
  have : Feas f p B = {μ : ↥B → ℝ | ∀ i, 0 ≤ μ i} ∩ ({μ | ∑ i, μ i = 1} ∩
      ({μ | ∀ w, ∑ i, μ i * ((i.1 w : ℤ) : ℝ) = p w} ∩
        {μ | ∀ i, f i.1 = ⊤ → μ i = 0})) := by
    ext μ; exact Iff.rfl
  rw [this]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (by fun_prop) continuous_const
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_eq (by fun_prop) continuous_const
  · rw [Set.setOf_forall]
    refine isClosed_iInter fun i => ?_
    by_cases h : f i.1 = ⊤
    · simp only [h, true_implies]
      exact isClosed_eq (continuous_apply i) continuous_const
    · simp only [h, false_implies, Set.setOf_true]
      exact isClosed_univ

lemma feas_compact : IsCompact (Feas f p B) := by
  refine (isCompact_univ_pi (fun _ : ↥B => isCompact_Icc (a := (0:ℝ)) (b := 1))).of_isClosed_subset
    (feas_closed f p B) ?_
  intro μ hμ
  simp only [Set.mem_univ_pi, Set.mem_Icc]
  intro i
  refine ⟨hμ.1 i, ?_⟩
  exact (Finset.single_le_sum (fun j _ => hμ.1 j) (Finset.mem_univ i)).trans hμ.2.1.le

/-- The main exchange argument: a minimizer of the value, chosen to minimize the potential
`Phi` among minimizers, is supported on the integral neighborhood of `p`. -/
theorem exists_good (hf : MNaturalConvex f)
    (hB : ∀ y ∈ B, ∀ y' ∈ B, ∀ z : V → ℤ,
      (∀ v, (y v ≤ z v ∨ y' v ≤ z v) ∧ (z v ≤ y v ∨ z v ≤ y' v)) → z ∈ B)
    (hne : (Feas f p B).Nonempty) :
    ∃ μ ∈ Feas f p B, (∀ ν ∈ Feas f p B, Val f B μ ≤ Val f B ν) ∧
      (∀ i, 0 < μ i → (i : V → ℤ) ∈ IntegralNeighborhoodFinset p) := by
  obtain ⟨μ1, hμ1, hmin1⟩ := (feas_compact f p B).exists_isMinOn hne (val_continuous f B).continuousOn
  have hmin1' : ∀ ν ∈ Feas f p B, Val f B μ1 ≤ Val f B ν := fun ν hν => (isMinOn_iff.mp hmin1) ν hν
  set M : Set (↥B → ℝ) := Feas f p B ∩ {μ | Val f B μ = Val f B μ1} with hM
  have hMc : IsCompact M := (feas_compact f p B).inter_right
    (isClosed_eq (val_continuous f B) continuous_const)
  have hMne : M.Nonempty := ⟨μ1, hμ1, rfl⟩
  obtain ⟨μ, ⟨hμF, hμV⟩, hminΦ⟩ := hMc.exists_isMinOn hMne (phi_continuous p B).continuousOn
  have hμ0 : ∀ i, 0 ≤ μ i := hμF.1
  have hμ1 : ∑ i, μ i = 1 := hμF.2.1
  have hμ2 : ∀ w, ∑ i, μ i * ((i.1 w : ℤ) : ℝ) = p w := hμF.2.2.1
  have hμ3 : ∀ i, f i.1 = ⊤ → μ i = 0 := hμF.2.2.2
  have hminΦ' : ∀ ν ∈ M, Phi p B μ ≤ Phi p B ν := fun ν hν => (isMinOn_iff.mp hminΦ) ν hν
  refine ⟨μ, hμF, fun ν hν => hμV ▸ hmin1' ν hν, ?_⟩
  intro i hi
  by_contra hcon
  simp only [IntegralNeighborhoodFinset, Fintype.mem_piFinset, Finset.mem_Icc] at hcon
  push_neg at hcon
  obtain ⟨w, hw⟩ := hcon
  -- the set of positive-weight points
  set T : Finset ↥B := Finset.univ.filter (fun j => 0 < μ j) with hT
  have hiT : i ∈ T := by simp [hT, hi]
  have hTne : T.Nonempty := ⟨i, hiT⟩
  obtain ⟨a, haT, hamax⟩ := T.exists_max_image (fun j : ↥B => j.1 w) hTne
  obtain ⟨b, hbT, hbmin⟩ := T.exists_min_image (fun j : ↥B => j.1 w) hTne
  have hmemT : ∀ j, j ∈ T ↔ 0 < μ j := by intro j; simp [hT]
  have hμa : 0 < μ a := (hmemT a).mp haT
  have hμb : 0 < μ b := (hmemT b).mp hbT
  have hzero : ∑ j, μ j * (((j.1 w : ℤ) : ℝ) - p w) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ2 w, hμ1]; ring
  have hzero' : ∑ j, μ j * (p w - ((j.1 w : ℤ) : ℝ)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ2 w, hμ1]; ring
  -- key gap: b w + 2 ≤ a w
  have hab : (b : V → ℤ) w + 2 ≤ (a : V → ℤ) w := by
    rcases lt_or_ge ((i : V → ℤ) w) ⌊p w⌋ with hB1 | hA1
    · -- case B: i w < ⌊p w⌋
      have hbi : (b : V → ℤ) w ≤ (i : V → ℤ) w := hbmin i hiT
      have hbp : ((b : V → ℤ) w : ℝ) < p w := by
        have : ((b : V → ℤ) w : ℝ) < (⌊p w⌋ : ℝ) := by exact_mod_cast (lt_of_le_of_lt hbi hB1)
        exact this.trans_le (Int.floor_le (p w))
      obtain ⟨j, hj, hjc⟩ := avg_lemma μ _ hμ0 hzero' b hμb (by show 0 < p w - ((b.1 w : ℤ) : ℝ); linarith)
      have hja : ((j : V → ℤ) w) ≤ (a : V → ℤ) w := hamax j ((hmemT j).mpr hj)
      have hpa : p w < ((a : V → ℤ) w : ℝ) := by
        have : ((j.1 w : ℤ) : ℝ) ≤ ((a : V → ℤ) w : ℝ) := by exact_mod_cast hja
        linarith
      have h1 : ⌊p w⌋ < (a : V → ℤ) w := Int.floor_lt.mpr hpa
      omega
    · have hA2 : ⌈p w⌉ < (i : V → ℤ) w := hw hA1
      have hai : (i : V → ℤ) w ≤ (a : V → ℤ) w := hamax i hiT
      have hap : p w < ((a : V → ℤ) w : ℝ) := by
        have : (⌈p w⌉ : ℝ) < ((a : V → ℤ) w : ℝ) := by exact_mod_cast (lt_of_lt_of_le hA2 hai)
        exact (Int.le_ceil (p w)).trans_lt this
      obtain ⟨j, hj, hjc⟩ := avg_lemma μ _ hμ0 hzero a hμa (by show 0 < ((a.1 w : ℤ) : ℝ) - p w; linarith)
      have hjb : (b : V → ℤ) w ≤ ((j : V → ℤ) w) := hbmin j ((hmemT j).mpr hj)
      have hpb : ((b : V → ℤ) w : ℝ) < p w := by
        have : ((b : V → ℤ) w : ℝ) ≤ ((j.1 w : ℤ) : ℝ) := by exact_mod_cast hjb
        linarith
      have h1 : (b : V → ℤ) w < ⌈p w⌉ := Int.lt_ceil.mpr hpb
      omega
  have hab_ne : a ≠ b := by
    intro h; rw [h] at hab; omega
  have hfa : f (a : V → ℤ) ≠ ⊤ := fun h => by have := hμ3 a h; linarith
  have hfb : f (b : V → ℤ) ≠ ⊤ := fun h => by have := hμ3 b h; linarith
  obtain ⟨d, hdu, hdw, hineq⟩ := mnat_exc f hf a b hfa hfb w (by omega)
  set a' : V → ℤ := fun w' => (a : V → ℤ) w' - d w' with ha'
  set b' : V → ℤ := fun w' => (b : V → ℤ) w' + d w' with hb'
  have ha'B : a' ∈ B := by
    refine hB a a.2 b b.2 a' ?_
    intro v
    simp only [ha']
    rcases hdw v with h | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
  have hb'B : b' ∈ B := by
    refine hB a a.2 b b.2 b' ?_
    intro v
    simp only [hb']
    rcases hdw v with h | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
  have hsum_ne : f (a : V → ℤ) + f (b : V → ℤ) ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hfa, hfb⟩
  have hsum'_ne : f a' + f b' ≠ ⊤ := ne_top_of_le_ne_top hsum_ne hineq
  obtain ⟨hfa', hfb'⟩ := WithTop.add_ne_top.mp hsum'_ne
  set A' : ↥B := ⟨a', ha'B⟩ with hA'
  set B' : ↥B := ⟨b', hb'B⟩ with hB'
  set m : ℝ := min (μ a) (μ b) with hm
  have hm_pos : 0 < m := lt_min hμa hμb
  have hma : m ≤ μ a := min_le_left _ _
  have hmb : m ≤ μ b := min_le_right _ _
  set ν : ↥B → ℝ := fun i => μ i + m * ((if i = A' then (1:ℝ) else 0) + (if i = B' then 1 else 0)
      - (if i = a then 1 else 0) - (if i = b then 1 else 0)) with hν
  have hν_shift : ∀ g : ↥B → ℝ, ∑ i, ν i * g i = ∑ i, μ i * g i + m * (g A' + g B' - g a - g b) :=
    fun g => sum_shift μ g m a b A' B'
  -- ν is feasible
  have hν_nonneg : ∀ i, 0 ≤ ν i := by
    intro i
    simp only [hν]
    have h1 : (0:ℝ) ≤ (if i = A' then (1:ℝ) else 0) := by split_ifs <;> norm_num
    have h2 : (0:ℝ) ≤ (if i = B' then (1:ℝ) else 0) := by split_ifs <;> norm_num
    have h0 := hμ0 i
    by_cases hia : i = a
    · rw [hia]
      have hab' : (a = b) = False := by simp [hab_ne]
      simp only [if_true, hab', if_false]
      rw [hia] at h1 h2
      nlinarith
    · by_cases hib : i = b
      · rw [hib]
        have hba' : (b = a) = False := by simp [hab_ne.symm]
        simp only [if_true, hba', if_false]
        rw [hib] at h1 h2
        nlinarith
      · simp only [if_neg hia, if_neg hib]
        nlinarith
  have hν_sum : ∑ i, ν i = 1 := by
    have := hν_shift (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hμ1]; ring
  have hν_coord : ∀ w', ∑ i, ν i * ((i.1 w' : ℤ) : ℝ) = p w' := by
    intro w'
    rw [hν_shift (fun i => ((i.1 w' : ℤ) : ℝ)), hμ2 w']
    simp only [hA', hB', ha', hb']
    push_cast; ring
  have hν_dom : ∀ i, f i.1 = ⊤ → ν i = 0 := by
    intro i hi
    have hia : i ≠ a := fun h => hfa (by rw [← h]; exact hi)
    have hib : i ≠ b := fun h => hfb (by rw [← h]; exact hi)
    have hiA : i ≠ A' := fun h => hfa' (by rw [h] at hi; exact hi)
    have hiB : i ≠ B' := fun h => hfb' (by rw [h] at hi; exact hi)
    simp only [hν, if_neg hia, if_neg hib, if_neg hiA, if_neg hiB, hμ3 i hi]; ring
  have hνF : ν ∈ Feas f p B := ⟨hν_nonneg, hν_sum, hν_coord, hν_dom⟩
  -- value does not increase
  obtain ⟨ra, hra⟩ := WithTop.ne_top_iff_exists.mp hfa
  obtain ⟨rb, hrb⟩ := WithTop.ne_top_iff_exists.mp hfb
  obtain ⟨ra', hra'⟩ := WithTop.ne_top_iff_exists.mp hfa'
  obtain ⟨rb', hrb'⟩ := WithTop.ne_top_iff_exists.mp hfb'
  have hrineq : ra' + rb' ≤ ra + rb := by
    rw [← hra, ← hrb, ← hra', ← hrb'] at hineq
    exact_mod_cast hineq
  have hVal : Val f B ν ≤ Val f B μ := by
    unfold Val
    rw [hν_shift]
    have e1 : (f (A' : V → ℤ)).untopD 0 = ra' := by
      show (f a').untopD 0 = ra'
      rw [← hra']; rfl
    have e2 : (f (B' : V → ℤ)).untopD 0 = rb' := by
      show (f b').untopD 0 = rb'
      rw [← hrb']; rfl
    have e3 : (f (a : V → ℤ)).untopD 0 = ra := by rw [← hra]; rfl
    have e4 : (f (b : V → ℤ)).untopD 0 = rb := by rw [← hrb]; rfl
    rw [e1, e2, e3, e4]
    nlinarith
  have hνM : ν ∈ M := ⟨hνF, le_antisymm (hμV ▸ hVal) (hmin1' ν hνF)⟩
  have hΦ := hminΦ' ν hνM
  -- but the potential strictly decreases
  have hΦν : Phi p B ν = Phi p B μ + m * ((∑ w', ((a' w' : ℝ) - p w') ^ 2) + (∑ w', ((b' w' : ℝ) - p w') ^ 2)
      - (∑ w', (((a : V → ℤ) w' : ℝ) - p w') ^ 2) - (∑ w', (((b : V → ℤ) w' : ℝ) - p w') ^ 2)) := by
    unfold Phi
    rw [hν_shift]
  have hdiff := phi_diff (a : V → ℤ) (b : V → ℤ) d p
  have hneg := phi_diff_neg (a : V → ℤ) (b : V → ℤ) d p w hdu hdw hab
  have hbr : (∑ w', ((a' w' : ℝ) - p w') ^ 2) + (∑ w', ((b' w' : ℝ) - p w') ^ 2)
      - (∑ w', (((a : V → ℤ) w' : ℝ) - p w') ^ 2) - (∑ w', (((b : V → ℤ) w' : ℝ) - p w') ^ 2) ≤ -2 := by
    simp only [ha', hb']
    rw [hdiff]; exact hneg
  have : m * ((∑ w', ((a' w' : ℝ) - p w') ^ 2) + (∑ w', ((b' w' : ℝ) - p w') ^ 2)
      - (∑ w', (((a : V → ℤ) w' : ℝ) - p w') ^ 2) - (∑ w', (((b : V → ℤ) w' : ℝ) - p w') ^ 2)) < 0 :=
    mul_neg_of_pos_of_neg hm_pos (by linarith)
  linarith

end Main

/-! ### Step 4: transfer back to representations over finsets. -/

def CCSet (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ) : Set (WithTop ℝ) :=
  {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
    (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ f) ∧
    (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
    L = ((∑ y ∈ S, lam y * (f y).untopD 0 : ℝ) : WithTop ℝ)}

lemma ccvOn_eq (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ) :
    ConvexClosureValOn f S x = sInf (CCSet f S x) := rfl

lemma ccset_bddBelow (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ) :
    BddBelow (CCSet f S x) := by
  refine ⟨((-(∑ y ∈ S, |(f y).untopD 0|) : ℝ) : WithTop ℝ), ?_⟩
  rintro L ⟨lam, h0, h1, -, -, rfl⟩
  rw [WithTop.coe_le_coe]
  have : ∀ y ∈ S, -|(f y).untopD 0| ≤ lam y * (f y).untopD 0 := by
    intro y hy
    have hl1 : lam y ≤ 1 := (Finset.single_le_sum h0 hy).trans h1.le
    have h2 := mul_le_mul_of_nonneg_left (neg_abs_le ((f y).untopD 0)) (h0 y hy)
    have h3 := mul_le_mul_of_nonneg_right hl1 (abs_nonneg ((f y).untopD 0))
    linarith
  calc -(∑ y ∈ S, |(f y).untopD 0|) = ∑ y ∈ S, -|(f y).untopD 0| := by rw [Finset.sum_neg_distrib]
    _ ≤ _ := Finset.sum_le_sum this

lemma ccvOn_le_of (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ)
    (lam : (V → ℤ) → ℝ) (h0 : ∀ y ∈ S, 0 ≤ lam y) (h1 : ∑ y ∈ S, lam y = 1)
    (hd : ∀ y ∈ S, y ∈ DomZ f) (h2 : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) :
    ConvexClosureValOn f S x ≤ ((∑ y ∈ S, lam y * (f y).untopD 0 : ℝ) : WithTop ℝ) := by
  rw [ccvOn_eq]
  exact csInf_le (ccset_bddBelow f S x) ⟨lam, h0, h1, hd, h2, rfl⟩

/-- The local representation lemma. -/
theorem local_le (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) (p : V → ℝ)
    (S : Finset (V → ℤ)) (hS : ∀ y ∈ S, y ∈ DomZ f)
    (lam : (V → ℤ) → ℝ) (h0 : ∀ y ∈ S, 0 ≤ lam y) (h1 : ∑ y ∈ S, lam y = 1)
    (h2 : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = p v) :
    ∃ lam' : (V → ℤ) → ℝ,
      (∀ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p), 0 ≤ lam' y) ∧
      (∑ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p), lam' y = 1) ∧
      (∀ v, ∑ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p),
        lam' y * (y v : ℝ) = p v) ∧
      ∑ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p),
        lam' y * (f y).untopD 0 ≤ ∑ y ∈ S, lam y * (f y).untopD 0 := by
  set S0 := Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p) with hS0
  set B := boxOf S with hBdef
  have hSB : S ⊆ B := subset_boxOf S
  -- the initial feasible point
  set μ0 : ↥B → ℝ := fun i => if i.1 ∈ S then lam i else 0 with hμ0
  have hres : ∀ g : (V → ℤ) → ℝ, ∑ i : ↥B, μ0 i * g i = ∑ y ∈ S, lam y * g y := by
    intro g
    have e1 : ∑ i : ↥B, μ0 i * g i = ∑ y ∈ B, (if y ∈ S then lam y * g y else 0) := by
      rw [← Finset.sum_coe_sort B (fun y => if y ∈ S then lam y * g y else 0)]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hμ0]; split_ifs <;> simp
    rw [e1, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSB]
  have hμ0F : μ0 ∈ Feas f p B := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; simp only [hμ0]; split_ifs with h
      · exact h0 _ h
      · exact le_rfl
    · have := hres (fun _ => 1); simp only [mul_one] at this; rw [this, h1]
    · intro w; rw [hres (fun y => (y w : ℝ))]; exact h2 w
    · intro i hi
      simp only [hμ0]
      rw [if_neg]
      intro h; exact hS _ h hi
  have hBc : ∀ y ∈ B, ∀ y' ∈ B, ∀ z : V → ℤ,
      (∀ v, (y v ≤ z v ∨ y' v ≤ z v) ∧ (z v ≤ y v ∨ z v ≤ y' v)) → z ∈ B :=
    fun y hy y' hy' z hz => boxOf_closed S y y' z hy hy' hz
  obtain ⟨μ, hμF, hμmin, hμsupp⟩ := exists_good f p B hf hBc ⟨μ0, hμ0F⟩
  have hμ0 : ∀ i, 0 ≤ μ i := hμF.1
  have hμ1 : ∑ i, μ i = 1 := hμF.2.1
  have hμ2 : ∀ w, ∑ i, μ i * ((i.1 w : ℤ) : ℝ) = p w := hμF.2.2.1
  have hμ3 : ∀ i, f i.1 = ⊤ → μ i = 0 := hμF.2.2.2
  set lam' : (V → ℤ) → ℝ := fun y => if h : y ∈ B then μ ⟨y, h⟩ else 0 with hlam'
  have hlam'_nonneg : ∀ y, 0 ≤ lam' y := by
    intro y; simp only [hlam']; split_ifs
    · exact hμ0 _
    · exact le_rfl
  have hμ_zero : ∀ i : ↥B, (i : V → ℤ) ∉ S0 → μ i = 0 := by
    intro i hi
    rcases (hμ0 i).lt_or_eq with h | h
    · exfalso
      apply hi
      rw [hS0, Finset.mem_filter]
      refine ⟨hμsupp i h, ?_⟩
      intro htop
      have := hμ3 i htop
      linarith
    · exact h.symm
  have hres' : ∀ g : (V → ℤ) → ℝ, ∑ y ∈ S0, lam' y * g y = ∑ i : ↥B, μ i * g i := by
    intro g
    have e1 : ∑ i : ↥B, μ i * g i = ∑ y ∈ B, lam' y * g y := by
      rw [← Finset.sum_coe_sort B (fun y => lam' y * g y)]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hlam', dif_pos i.2]
    have e2 : ∑ y ∈ S0 ∩ B, lam' y * g y = ∑ y ∈ B, lam' y * g y := by
      apply Finset.sum_subset Finset.inter_subset_right
      intro y hyB hy
      have hyS0 : y ∉ S0 := fun h => hy (Finset.mem_inter.mpr ⟨h, hyB⟩)
      simp only [hlam', dif_pos hyB]
      rw [hμ_zero ⟨y, hyB⟩ hyS0, zero_mul]
    have e3 : ∑ y ∈ S0 ∩ B, lam' y * g y = ∑ y ∈ S0, lam' y * g y := by
      apply Finset.sum_subset Finset.inter_subset_left
      intro y hyS0 hy
      have hyB : y ∉ B := fun h => hy (Finset.mem_inter.mpr ⟨hyS0, h⟩)
      simp only [hlam', dif_neg hyB, zero_mul]
    rw [e1, ← e2, e3]
  refine ⟨lam', fun y _ => hlam'_nonneg y, ?_, ?_, ?_⟩
  · have := hres' (fun _ => 1); simp only [mul_one] at this; rw [this, hμ1]
  · intro v; rw [hres' (fun y => (y v : ℝ))]; exact hμ2 v
  · rw [hres' (fun y => (f y).untopD 0), ← hres (fun y => (f y).untopD 0)]
    exact hμmin μ0 hμ0F

theorem key (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) (p : V → ℝ)
    (S : Finset (V → ℤ)) (hS : ∀ y ∈ S, y ∈ DomZ f) :
    ConvexClosureValOn f (Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p)) p
      ≤ ConvexClosureValOn f S p := by
  rw [ccvOn_eq f S p]
  rcases (CCSet f S p).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, WithTop.sInf_empty]; exact le_top
  · refine le_csInf hne ?_
    rintro L ⟨lam, h0, h1, -, h2, rfl⟩
    obtain ⟨lam', h0', h1', h2', hval⟩ := local_le f hf p S hS lam h0 h1 h2
    refine (ccvOn_le_of f _ p lam' h0' h1' (fun y hy => (Finset.mem_filter.mp hy).2) h2').trans ?_
    exact WithTop.coe_le_coe.mpr hval

theorem integrally_convex_core (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    IsIntegrallyConvexFunction f := by
  unfold IsIntegrallyConvexFunction
  intro p
  set S0 := Finset.filter (fun y => y ∈ DomZ f) (IntegralNeighborhoodFinset p) with hS0
  have hS0d : ∀ y ∈ S0, y ∈ DomZ f := fun y hy => (Finset.mem_filter.mp hy).2
  have hkey := key f hf p
  apply le_antisymm
  · unfold ConvexClosureVal
    apply csInf_le
    · exact ⟨ConvexClosureValOn f S0 p, by rintro L ⟨S, hS, rfl⟩; exact hkey S hS⟩
    · exact ⟨S0, hS0d, rfl⟩
  · unfold ConvexClosureVal
    refine le_csInf ⟨ConvexClosureValOn f S0 p, S0, hS0d, rfl⟩ ?_
    rintro L ⟨S, hS, rfl⟩; exact hkey S hS

lemma nbhd_int (x : V → ℤ) : IntegralNeighborhoodFinset (fun v => (x v : ℝ)) = {x} := by
  ext y
  simp [IntegralNeighborhoodFinset, Fintype.mem_piFinset, Finset.Icc_self, funext_iff]

theorem convex_extensible_core (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    ConvexExtensible f := by
  unfold ConvexExtensible
  intro x
  rw [integrally_convex_core f hf (fun v => (x v : ℝ)), nbhd_int]
  by_cases hx : x ∈ DomZ f
  · rw [Finset.filter_singleton, if_pos hx]
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
    rw [← hr]
    apply le_antisymm
    · refine (ccvOn_le_of f {x} _ (fun _ => 1) (by simp) (by simp) (by simpa using hx)
        (by simp)).trans ?_
      simp [← hr]
    · rw [ccvOn_eq]
      refine le_csInf ⟨_, (fun _ => 1), by simp, by simp, by simpa using hx, by simp, rfl⟩ ?_
      rintro L ⟨lam, -, h1, -, -, rfl⟩
      simp only [Finset.sum_singleton] at h1
      simp [h1, ← hr]
  · rw [Finset.filter_singleton, if_neg hx]
    have hx' : f x = ⊤ := by simpa [DomZ] using hx
    rw [hx', ccvOn_eq]
    have : CCSet f ∅ (fun v => (x v : ℝ)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro L ⟨lam, -, h1, -⟩
      simp at h1
    rw [this, WithTop.sInf_empty]

theorem mnat_convex_integrally_convex_core (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    IsIntegrallyConvexFunction f ∧ ConvexExtensible f :=
  ⟨integrally_convex_core f hf, convex_extensible_core f hf⟩

end DiscreteConvex.MConvexFunctionsC

open DiscreteConvex.MConvexFunctionsC


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f) :
    IsIntegrallyConvexFunction f ∧ ConvexExtensible f := by
  exact mnat_convex_integrally_convex_core f hf
