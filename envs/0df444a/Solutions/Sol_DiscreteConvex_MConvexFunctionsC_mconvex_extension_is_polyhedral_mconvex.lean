-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsC.mconvex_extension_is_polyhedral_mconvex
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T04:10:59.327771+00:00
-- url     : https://prove2.me/submissions/e7a833ca-ac92-4f60-a2a7-4d6f265b81bc

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsPolyhedralConvex

set_option autoImplicit false

namespace MConvexExtPoly

open scoped Pointwise
open Classical
open DiscreteConvex.MConvexFunctionsC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Part 1: Local representation on the integral neighborhood -/

noncomputable def IntNbhd (p : V → ℝ) : Finset (V → ℤ) :=
  Fintype.piFinset (fun v => Finset.Icc ⌊p v⌋ ⌈p v⌉)

lemma mem_intNbhd {p : V → ℝ} {y : V → ℤ} :
    y ∈ IntNbhd p ↔ ∀ v, ⌊p v⌋ ≤ y v ∧ y v ≤ ⌈p v⌉ := by
  simp [IntNbhd, Fintype.mem_piFinset, Finset.mem_Icc]

theorem mexch_dir (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (a b : V → ℤ)
    (ha : f a ≠ ⊤) (hb : f b ≠ ⊤) (u : V) (hu : b u < a u) :
    ∃ d : V → ℤ, d u = 1 ∧ (∀ w, d w = 0 ∨ (d w = 1 ∧ b w < a w) ∨ (d w = -1 ∧ a w < b w)) ∧
      f (fun w => a w - d w) + f (fun w => b w + d w) ≤ f a + f b := by
  have hu' : u ∈ SuppPos a b := by simp [SuppPos, hu]
  obtain ⟨v, hv, hineq⟩ := hf a ha b hb u hu'
  simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have huv : u ≠ v := by intro h; subst h; omega
  refine ⟨fun w => CharVec u w - CharVec v w, by simp [CharVec, huv], ?_, ?_⟩
  · intro w; simp only [CharVec]; split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) huv
    · right; left; exact ⟨by norm_num, h1 ▸ hu⟩
    · right; right; exact ⟨by norm_num, h2 ▸ hv⟩
    · left; norm_num
  · convert hineq using 2 <;> (congr 1; funext w; ring)

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

lemma phi_diff_neg (a b d : V → ℤ) (u : V) (hdu : d u = 1)
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
  exact ⟨by linarith [neg_abs_le (y v)], by linarith [le_abs_self (y v)]⟩

lemma boxOf_closed (S : Finset (V → ℤ)) (y y' z : V → ℤ) (hy : y ∈ boxOf S) (hy' : y' ∈ boxOf S)
    (hz : ∀ v, (y v ≤ z v ∨ y' v ≤ z v) ∧ (z v ≤ y v ∨ z v ≤ y' v)) : z ∈ boxOf S := by
  rw [mem_boxOf] at *
  intro v
  have h1 := hy v; have h2 := hy' v; have h3 := hz v
  constructor <;> omega

section BoxOpt

variable (f : (V → ℤ) → WithTop ℝ) (p : V → ℝ) (B : Finset (V → ℤ))

def Feas : Set (↥B → ℝ) :=
  {μ | (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i = 1) ∧ (∀ w, ∑ i, μ i * ((i.1 w : ℤ) : ℝ) = p w) ∧
    (∀ i, f i.1 = ⊤ → μ i = 0)}

def Val (μ : ↥B → ℝ) : ℝ := ∑ i, μ i * (f i.1).untopD 0

def Phi (μ : ↥B → ℝ) : ℝ := ∑ i, μ i * ∑ w, (((i.1 w : ℤ) : ℝ) - p w) ^ 2

lemma val_continuous : Continuous (Val f B) := by unfold Val; fun_prop

lemma phi_continuous : Continuous (Phi p B) := by unfold Phi; fun_prop

lemma feas_closed : IsClosed (Feas f p B) := by
  have : Feas f p B = {μ : ↥B → ℝ | ∀ i, 0 ≤ μ i} ∩ ({μ | ∑ i, μ i = 1} ∩
      ({μ | ∀ w, ∑ i, μ i * ((i.1 w : ℤ) : ℝ) = p w} ∩
        {μ | ∀ i, f i.1 = ⊤ → μ i = 0})) := by ext μ; exact Iff.rfl
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
  exact ⟨hμ.1 i, (Finset.single_le_sum (fun j _ => hμ.1 j) (Finset.mem_univ i)).trans hμ.2.1.le⟩

theorem exists_good (hf : MExchangeAxiom f)
    (hB : ∀ y ∈ B, ∀ y' ∈ B, ∀ z : V → ℤ,
      (∀ v, (y v ≤ z v ∨ y' v ≤ z v) ∧ (z v ≤ y v ∨ z v ≤ y' v)) → z ∈ B)
    (hne : (Feas f p B).Nonempty) :
    ∃ μ ∈ Feas f p B, (∀ ν ∈ Feas f p B, Val f B μ ≤ Val f B ν) ∧
      (∀ i, 0 < μ i → (i : V → ℤ) ∈ IntNbhd p) := by
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
  rw [mem_intNbhd] at hcon
  push_neg at hcon
  obtain ⟨w, hw⟩ := hcon
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
  have hab : (b : V → ℤ) w + 2 ≤ (a : V → ℤ) w := by
    rcases lt_or_ge ((i : V → ℤ) w) ⌊p w⌋ with hB1 | hA1
    · have hbi : (b : V → ℤ) w ≤ (i : V → ℤ) w := hbmin i hiT
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
  have hab_ne : a ≠ b := by intro h; rw [h] at hab; omega
  have hfa : f (a : V → ℤ) ≠ ⊤ := fun h => by have := hμ3 a h; linarith
  have hfb : f (b : V → ℤ) ≠ ⊤ := fun h => by have := hμ3 b h; linarith
  obtain ⟨d, hdu, hdw, hineq⟩ := mexch_dir f hf a b hfa hfb w (by omega)
  set a' : V → ℤ := fun w' => (a : V → ℤ) w' - d w' with ha'
  set b' : V → ℤ := fun w' => (b : V → ℤ) w' + d w' with hb'
  have ha'B : a' ∈ B := by
    refine hB a a.2 b b.2 a' (fun v => ?_)
    simp only [ha']; rcases hdw v with h | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
  have hb'B : b' ∈ B := by
    refine hB a a.2 b b.2 b' (fun v => ?_)
    simp only [hb']; rcases hdw v with h | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
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
  have hν_nonneg : ∀ i, 0 ≤ ν i := by
    intro i; simp only [hν]
    have h1 : (0:ℝ) ≤ (if i = A' then (1:ℝ) else 0) := by split_ifs <;> norm_num
    have h2 : (0:ℝ) ≤ (if i = B' then (1:ℝ) else 0) := by split_ifs <;> norm_num
    have h0 := hμ0 i
    by_cases hia : i = a
    · rw [hia]
      have hab' : (a = b) = False := by simp [hab_ne]
      simp only [if_true, hab', if_false]
      rw [hia] at h1 h2; nlinarith
    · by_cases hib : i = b
      · rw [hib]
        have hba' : (b = a) = False := by simp [hab_ne.symm]
        simp only [if_true, hba', if_false]
        rw [hib] at h1 h2; nlinarith
      · simp only [if_neg hia, if_neg hib]; nlinarith
  have hν_sum : ∑ i, ν i = 1 := by
    have := hν_shift (fun _ => 1); simp only [mul_one] at this; rw [this, hμ1]; ring
  have hν_coord : ∀ w', ∑ i, ν i * ((i.1 w' : ℤ) : ℝ) = p w' := by
    intro w'; rw [hν_shift (fun i => ((i.1 w' : ℤ) : ℝ)), hμ2 w']
    simp only [hA', hB', ha', hb']; push_cast; ring
  have hν_dom : ∀ i, f i.1 = ⊤ → ν i = 0 := by
    intro i hi
    have hia : i ≠ a := fun h => hfa (by rw [← h]; exact hi)
    have hib : i ≠ b := fun h => hfb (by rw [← h]; exact hi)
    have hiA : i ≠ A' := fun h => hfa' (by rw [h] at hi; exact hi)
    have hiB : i ≠ B' := fun h => hfb' (by rw [h] at hi; exact hi)
    simp only [hν, if_neg hia, if_neg hib, if_neg hiA, if_neg hiB, hμ3 i hi]; ring
  have hνF : ν ∈ Feas f p B := ⟨hν_nonneg, hν_sum, hν_coord, hν_dom⟩
  obtain ⟨ra, hra⟩ := WithTop.ne_top_iff_exists.mp hfa
  obtain ⟨rb, hrb⟩ := WithTop.ne_top_iff_exists.mp hfb
  obtain ⟨ra', hra'⟩ := WithTop.ne_top_iff_exists.mp hfa'
  obtain ⟨rb', hrb'⟩ := WithTop.ne_top_iff_exists.mp hfb'
  have hrineq : ra' + rb' ≤ ra + rb := by
    rw [← hra, ← hrb, ← hra', ← hrb'] at hineq; exact_mod_cast hineq
  have hVal : Val f B ν ≤ Val f B μ := by
    unfold Val; rw [hν_shift]
    have e1 : (f (A' : V → ℤ)).untopD 0 = ra' := by show (f a').untopD 0 = ra'; rw [← hra']; rfl
    have e2 : (f (B' : V → ℤ)).untopD 0 = rb' := by show (f b').untopD 0 = rb'; rw [← hrb']; rfl
    have e3 : (f (a : V → ℤ)).untopD 0 = ra := by rw [← hra]; rfl
    have e4 : (f (b : V → ℤ)).untopD 0 = rb := by rw [← hrb]; rfl
    rw [e1, e2, e3, e4]; nlinarith
  have hνM : ν ∈ M := ⟨hνF, le_antisymm (hμV ▸ hVal) (hmin1' ν hνF)⟩
  have hΦ := hminΦ' ν hνM
  have hΦν : Phi p B ν = Phi p B μ + m * ((∑ w', ((a' w' : ℝ) - p w') ^ 2) + (∑ w', ((b' w' : ℝ) - p w') ^ 2)
      - (∑ w', (((a : V → ℤ) w' : ℝ) - p w') ^ 2) - (∑ w', (((b : V → ℤ) w' : ℝ) - p w') ^ 2)) := by
    unfold Phi; rw [hν_shift]
  have hdiff := phi_diff (a : V → ℤ) (b : V → ℤ) d p
  have hneg := phi_diff_neg (a : V → ℤ) (b : V → ℤ) d w hdu hdw hab
  have hbr : (∑ w', ((a' w' : ℝ) - p w') ^ 2) + (∑ w', ((b' w' : ℝ) - p w') ^ 2)
      - (∑ w', (((a : V → ℤ) w' : ℝ) - p w') ^ 2) - (∑ w', (((b : V → ℤ) w' : ℝ) - p w') ^ 2) ≤ -2 := by
    simp only [ha', hb']; rw [hdiff]; exact hneg
  have : m * ((∑ w', ((a' w' : ℝ) - p w') ^ 2) + (∑ w', ((b' w' : ℝ) - p w') ^ 2)
      - (∑ w', (((a : V → ℤ) w' : ℝ) - p w') ^ 2) - (∑ w', (((b : V → ℤ) w' : ℝ) - p w') ^ 2)) < 0 :=
    mul_neg_of_pos_of_neg hm_pos (by linarith)
  linarith

end BoxOpt

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

theorem local_le (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (p : V → ℝ)
    (S : Finset (V → ℤ)) (hS : ∀ y ∈ S, y ∈ DomZ f)
    (lam : (V → ℤ) → ℝ) (h0 : ∀ y ∈ S, 0 ≤ lam y) (h1 : ∑ y ∈ S, lam y = 1)
    (h2 : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = p v) :
    ∃ lam' : (V → ℤ) → ℝ,
      (∀ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p), 0 ≤ lam' y) ∧
      (∑ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p), lam' y = 1) ∧
      (∀ v, ∑ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p),
        lam' y * (y v : ℝ) = p v) ∧
      ∑ y ∈ Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p),
        lam' y * (f y).untopD 0 ≤ ∑ y ∈ S, lam y * (f y).untopD 0 := by
  set S0 := Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p) with hS0
  set B := boxOf S
  have hSB : S ⊆ B := subset_boxOf S
  set μ0 : ↥B → ℝ := fun i => if i.1 ∈ S then lam i else 0 with hμ0
  have hres : ∀ g : (V → ℤ) → ℝ, ∑ i : ↥B, μ0 i * g i = ∑ y ∈ S, lam y * g y := by
    intro g
    have e1 : ∑ i : ↥B, μ0 i * g i = ∑ y ∈ B, (if y ∈ S then lam y * g y else 0) := by
      rw [← Finset.sum_coe_sort B (fun y => if y ∈ S then lam y * g y else 0)]
      apply Finset.sum_congr rfl; intro i _; simp only [hμ0]; split_ifs <;> simp
    rw [e1, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSB]
  have hμ0F : μ0 ∈ Feas f p B := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; simp only [hμ0]; split_ifs with h
      · exact h0 _ h
      · exact le_rfl
    · have := hres (fun _ => 1); simp only [mul_one] at this; rw [this, h1]
    · intro w; rw [hres (fun y => (y w : ℝ))]; exact h2 w
    · intro i hi; simp only [hμ0]; rw [if_neg]; intro h; exact hS _ h hi
  have hBc : ∀ y ∈ B, ∀ y' ∈ B, ∀ z : V → ℤ,
      (∀ v, (y v ≤ z v ∨ y' v ≤ z v) ∧ (z v ≤ y v ∨ z v ≤ y' v)) → z ∈ B :=
    fun y hy y' hy' z hz => boxOf_closed S y y' z hy hy' hz
  obtain ⟨μ, hμF, hμmin, hμsupp⟩ := exists_good f p B hf hBc ⟨μ0, hμ0F⟩
  have hμ0' : ∀ i, 0 ≤ μ i := hμF.1
  have hμ1' : ∑ i, μ i = 1 := hμF.2.1
  have hμ2' : ∀ w, ∑ i, μ i * ((i.1 w : ℤ) : ℝ) = p w := hμF.2.2.1
  have hμ3' : ∀ i, f i.1 = ⊤ → μ i = 0 := hμF.2.2.2
  set lam' : (V → ℤ) → ℝ := fun y => if h : y ∈ B then μ ⟨y, h⟩ else 0 with hlam'
  have hlam'_nonneg : ∀ y, 0 ≤ lam' y := by
    intro y; simp only [hlam']; split_ifs
    · exact hμ0' _
    · exact le_rfl
  have hμ_zero : ∀ i : ↥B, (i : V → ℤ) ∉ S0 → μ i = 0 := by
    intro i hi
    rcases (hμ0' i).lt_or_eq with h | h
    · exfalso; apply hi; rw [hS0, Finset.mem_filter]
      refine ⟨hμsupp i h, fun htop => ?_⟩
      have := hμ3' i htop; linarith
    · exact h.symm
  have hres' : ∀ g : (V → ℤ) → ℝ, ∑ y ∈ S0, lam' y * g y = ∑ i : ↥B, μ i * g i := by
    intro g
    have e1 : ∑ i : ↥B, μ i * g i = ∑ y ∈ B, lam' y * g y := by
      rw [← Finset.sum_coe_sort B (fun y => lam' y * g y)]
      apply Finset.sum_congr rfl; intro i _; simp only [hlam', dif_pos i.2]
    have e2 : ∑ y ∈ S0 ∩ B, lam' y * g y = ∑ y ∈ B, lam' y * g y := by
      apply Finset.sum_subset Finset.inter_subset_right
      intro y hyB hy
      have hyS0 : y ∉ S0 := fun h => hy (Finset.mem_inter.mpr ⟨h, hyB⟩)
      simp only [hlam', dif_pos hyB]; rw [hμ_zero ⟨y, hyB⟩ hyS0, zero_mul]
    have e3 : ∑ y ∈ S0 ∩ B, lam' y * g y = ∑ y ∈ S0, lam' y * g y := by
      apply Finset.sum_subset Finset.inter_subset_left
      intro y hyS0 hy
      have hyB : y ∉ B := fun h => hy (Finset.mem_inter.mpr ⟨hyS0, h⟩)
      simp only [hlam', dif_neg hyB, zero_mul]
    rw [e1, ← e2, e3]
  refine ⟨lam', fun y _ => hlam'_nonneg y, ?_, ?_, ?_⟩
  · have := hres' (fun _ => 1); simp only [mul_one] at this; rw [this, hμ1']
  · intro v; rw [hres' (fun y => (y v : ℝ))]; exact hμ2' v
  · rw [hres' (fun y => (f y).untopD 0), ← hres (fun y => (f y).untopD 0)]
    exact hμmin μ0 hμ0F

theorem key_local (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (p : V → ℝ)
    (S : Finset (V → ℤ)) (hS : ∀ y ∈ S, y ∈ DomZ f) :
    ConvexClosureValOn f (Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p)) p
      ≤ ConvexClosureValOn f S p := by
  rw [ccvOn_eq f S p]
  rcases (CCSet f S p).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, WithTop.sInf_empty]; exact le_top
  · refine le_csInf hne ?_
    rintro L ⟨lam, h0, h1, -, h2, rfl⟩
    obtain ⟨lam', h0', h1', h2', hval⟩ := local_le f hf p S hS lam h0 h1 h2
    refine (ccvOn_le_of f _ p lam' h0' h1' (fun y hy => (Finset.mem_filter.mp hy).2) h2').trans ?_
    exact WithTop.coe_le_coe.mpr hval

theorem ccv_eq_local (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (p : V → ℝ) :
    ConvexClosureVal f p =
      ConvexClosureValOn f (Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p)) p := by
  set S0 := Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p)
  have hS0d : ∀ y ∈ S0, y ∈ DomZ f := fun y hy => (Finset.mem_filter.mp hy).2
  have hkey := key_local f hf p
  apply le_antisymm
  · unfold ConvexClosureVal
    apply csInf_le
    · exact ⟨ConvexClosureValOn f S0 p, by rintro L ⟨S, hS, rfl⟩; exact hkey S hS⟩
    · exact ⟨S0, hS0d, rfl⟩
  · unfold ConvexClosureVal
    refine le_csInf ⟨ConvexClosureValOn f S0 p, S0, hS0d, rfl⟩ ?_
    rintro L ⟨S, hS, rfl⟩; exact hkey S hS

theorem ccv_le_of (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (S : Finset (V → ℤ)) (x : V → ℝ)
    (lam : (V → ℤ) → ℝ) (h0 : ∀ y ∈ S, 0 ≤ lam y) (h1 : ∑ y ∈ S, lam y = 1)
    (hd : ∀ y ∈ S, y ∈ DomZ f) (h2 : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) :
    ConvexClosureVal f x ≤ ((∑ y ∈ S, lam y * (f y).untopD 0 : ℝ) : WithTop ℝ) := by
  rw [ccv_eq_local f hf x]
  exact (key_local f hf x S hd).trans (ccvOn_le_of f S x lam h0 h1 hd h2)

theorem exists_opt_rep (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (p : V → ℝ) (rp : ℝ)
    (hp : ConvexClosureVal f p = (rp : WithTop ℝ)) :
    ∃ μ : (V → ℤ) → ℝ,
      (∀ z, 0 ≤ μ z) ∧
      (∀ z ∉ Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p), μ z = 0) ∧
      (∑ z ∈ Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p), μ z = 1) ∧
      (∀ w, ∑ z ∈ Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p), μ z * (z w : ℝ) = p w) ∧
      (∑ z ∈ Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p), μ z * (f z).untopD 0 = rp) := by
  set S0 := Finset.filter (fun y => y ∈ DomZ f) (IntNbhd p) with hS0
  have hS0d : ∀ y ∈ S0, y ∈ DomZ f := fun y hy => (Finset.mem_filter.mp hy).2
  have hp0 : ConvexClosureValOn f S0 p = (rp : WithTop ℝ) := by
    rw [← ccv_eq_local f hf p, hp]
  have hne : (CCSet f S0 p).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [ccvOn_eq, h, WithTop.sInf_empty] at hp0
    exact WithTop.top_ne_coe hp0
  obtain ⟨_, ⟨lam0, h0, h1, -, h2, rfl⟩⟩ := hne
  have hne' : (CCSet f S0 p).Nonempty := ⟨_, ⟨lam0, h0, h1, hS0d, h2, rfl⟩⟩
  have hFne : (Feas f p S0).Nonempty := by
    refine ⟨fun i => lam0 i.1, fun i => h0 i.1 i.2, ?_, ?_, ?_⟩
    · exact (Finset.sum_coe_sort S0 lam0).trans h1
    · intro w; exact (Finset.sum_coe_sort S0 (fun y => lam0 y * (y w : ℝ))).trans (h2 w)
    · intro i hi; exfalso; exact hS0d i.1 i.2 hi
  obtain ⟨μ0, hμ0F, hmin⟩ := (feas_compact f p S0).exists_isMinOn hFne (val_continuous f S0).continuousOn
  have hmin' : ∀ ν ∈ Feas f p S0, Val f S0 μ0 ≤ Val f S0 ν := fun ν hν => (isMinOn_iff.mp hmin) ν hν
  set μ : (V → ℤ) → ℝ := fun z => if h : z ∈ S0 then μ0 ⟨z, h⟩ else 0 with hμ
  have hres : ∀ g : (V → ℤ) → ℝ, ∑ z ∈ S0, μ z * g z = ∑ i : ↥S0, μ0 i * g i.1 := by
    intro g
    rw [← Finset.sum_coe_sort S0 (fun z => μ z * g z)]
    apply Finset.sum_congr rfl; intro i _; simp only [hμ, dif_pos i.2]
  have hμ_nonneg : ∀ z, 0 ≤ μ z := by
    intro z; simp only [hμ]; split_ifs
    · exact hμ0F.1 _
    · exact le_rfl
  have hμ_supp : ∀ z ∉ S0, μ z = 0 := by intro z hz; simp [hμ, hz]
  have hμ_sum : ∑ z ∈ S0, μ z = 1 := by
    have := hres (fun _ => 1); simp only [mul_one] at this; rw [this, hμ0F.2.1]
  have hμ_coord : ∀ w, ∑ z ∈ S0, μ z * (z w : ℝ) = p w := by
    intro w; rw [hres (fun z => (z w : ℝ))]; exact hμ0F.2.2.1 w
  refine ⟨μ, hμ_nonneg, hμ_supp, hμ_sum, hμ_coord, ?_⟩
  have hle1 : ConvexClosureValOn f S0 p ≤ ((∑ z ∈ S0, μ z * (f z).untopD 0 : ℝ) : WithTop ℝ) :=
    ccvOn_le_of f S0 p μ (fun z _ => hμ_nonneg z) hμ_sum hS0d hμ_coord
  have hle2 : ((∑ z ∈ S0, μ z * (f z).untopD 0 : ℝ) : WithTop ℝ) ≤ ConvexClosureValOn f S0 p := by
    rw [ccvOn_eq]
    refine le_csInf hne' ?_
    rintro L ⟨lam, hl0, hl1, -, hl2, rfl⟩
    rw [WithTop.coe_le_coe, hres (fun z => (f z).untopD 0)]
    set ν0 : ↥S0 → ℝ := fun i => lam i.1
    have hν0F : ν0 ∈ Feas f p S0 := by
      refine ⟨fun i => hl0 i.1 i.2, ?_, ?_, ?_⟩
      · exact (Finset.sum_coe_sort S0 lam).trans hl1
      · intro w; exact (Finset.sum_coe_sort S0 (fun y => lam y * (y w : ℝ))).trans (hl2 w)
      · intro i hi; exfalso; exact hS0d i.1 i.2 hi
    have := hmin' ν0 hν0F
    unfold Val at this
    rw [← Finset.sum_coe_sort S0 (fun y => lam y * (f y).untopD 0)]
    exact this
  have heq : ((∑ z ∈ S0, μ z * (f z).untopD 0 : ℝ) : WithTop ℝ) = (rp : WithTop ℝ) := by
    rw [← hp0]; exact le_antisymm hle2 hle1
  exact WithTop.coe_inj.mp heq

/-! ### Part 2: ValidShift and ZeroShiftAt -/

noncomputable def UBox (f : (V → ℤ) → WithTop ℝ) (x y : V → ℝ) : Finset (V → ℤ) :=
  (Fintype.piFinset (fun w => Finset.Icc (min ⌊x w⌋ ⌊y w⌋ - 1) (max ⌈x w⌉ ⌈y w⌉ + 1))).filter
    (fun z => z ∈ DomZ f)

lemma mem_UBox {f : (V → ℤ) → WithTop ℝ} {x y : V → ℝ} {z : V → ℤ} :
    z ∈ UBox f x y ↔
      (∀ w, min ⌊x w⌋ ⌊y w⌋ - 1 ≤ z w ∧ z w ≤ max ⌈x w⌉ ⌈y w⌉ + 1) ∧ z ∈ DomZ f := by
  simp [UBox, Fintype.mem_piFinset, Finset.mem_Icc]

lemma subset_UBox_left (f : (V → ℤ) → WithTop ℝ) (x y : V → ℝ) :
    Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x) ⊆ UBox f x y := by
  intro z hz
  rw [Finset.mem_filter, mem_intNbhd] at hz
  rw [mem_UBox]
  refine ⟨fun w => ?_, hz.2⟩
  have h1 := (hz.1 w).1; have h2 := (hz.1 w).2
  have h3 := min_le_left ⌊x w⌋ ⌊y w⌋; have h4 := le_max_left ⌈x w⌉ ⌈y w⌉
  omega

lemma subset_UBox_right (f : (V → ℤ) → WithTop ℝ) (x y : V → ℝ) :
    Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y) ⊆ UBox f x y := by
  intro z hz
  rw [Finset.mem_filter, mem_intNbhd] at hz
  rw [mem_UBox]
  refine ⟨fun w => ?_, hz.2⟩
  have h1 := (hz.1 w).1; have h2 := (hz.1 w).2
  have h3 := min_le_right ⌊x w⌋ ⌊y w⌋; have h4 := le_max_right ⌈x w⌉ ⌈y w⌉
  omega

def ValidShift (f : (V → ℤ) → WithTop ℝ) (x y : V → ℝ) (μ ν : (V → ℤ) → ℝ) (d : V → ℝ) : Prop :=
  ∃ δμ δν : (V → ℤ) → ℝ,
    (∀ z ∈ UBox f x y, μ z = 0 → δμ z ≤ 0) ∧
    (∀ z ∈ UBox f x y, ν z = 0 → δν z ≤ 0) ∧
    (∑ z ∈ UBox f x y, δμ z = 0) ∧
    (∑ z ∈ UBox f x y, δν z = 0) ∧
    (∀ w : V, ∑ z ∈ UBox f x y, δμ z * (z w : ℝ) = d w) ∧
    (∀ w : V, ∑ z ∈ UBox f x y, δν z * (z w : ℝ) = -d w) ∧
    0 ≤ ∑ z ∈ UBox f x y, δμ z * (f z).untopD 0 + ∑ z ∈ UBox f x y, δν z * (f z).untopD 0

lemma validShift_zero (f : (V → ℤ) → WithTop ℝ) (x y : V → ℝ) (μ ν : (V → ℤ) → ℝ) :
    ValidShift f x y μ ν 0 := by
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, by simp, by simp, by simp, by simp, by simp⟩
  · intro _ _ _; exact le_rfl
  · intro _ _ _; exact le_rfl

lemma validShift_add {f : (V → ℤ) → WithTop ℝ} {x y : V → ℝ} {μ ν : (V → ℤ) → ℝ}
    {d1 d2 : V → ℝ} (h1 : ValidShift f x y μ ν d1) (h2 : ValidShift f x y μ ν d2) :
    ValidShift f x y μ ν (fun w => d1 w + d2 w) := by
  obtain ⟨δμ1, δν1, hμ1, hν1, hsμ1, hsν1, hmμ1, hmν1, hv1⟩ := h1
  obtain ⟨δμ2, δν2, hμ2, hν2, hsμ2, hsν2, hmμ2, hmν2, hv2⟩ := h2
  refine ⟨fun z => δμ1 z + δμ2 z, fun z => δν1 z + δν2 z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz h0; linarith [hμ1 z hz h0, hμ2 z hz h0]
  · intro z hz h0; linarith [hν1 z hz h0, hν2 z hz h0]
  · rw [Finset.sum_add_distrib, hsμ1, hsμ2, add_zero]
  · rw [Finset.sum_add_distrib, hsν1, hsν2, add_zero]
  · intro w
    have : ∀ z, (δμ1 z + δμ2 z) * (z w : ℝ) = δμ1 z * (z w : ℝ) + δμ2 z * (z w : ℝ) :=
      fun z => add_mul _ _ _
    simp_rw [this, Finset.sum_add_distrib, hmμ1 w, hmμ2 w]
  · intro w
    have : ∀ z, (δν1 z + δν2 z) * (z w : ℝ) = δν1 z * (z w : ℝ) + δν2 z * (z w : ℝ) :=
      fun z => add_mul _ _ _
    simp_rw [this, Finset.sum_add_distrib, hmν1 w, hmν2 w]; ring
  · have e1 : ∀ z, (δμ1 z + δμ2 z) * (f z).untopD 0 =
        δμ1 z * (f z).untopD 0 + δμ2 z * (f z).untopD 0 := fun z => add_mul _ _ _
    have e2 : ∀ z, (δν1 z + δν2 z) * (f z).untopD 0 =
        δν1 z * (f z).untopD 0 + δν2 z * (f z).untopD 0 := fun z => add_mul _ _ _
    simp_rw [e1, e2, Finset.sum_add_distrib]
    linarith

noncomputable def stepBound (m δ : ℝ) : ℝ :=
  if 0 < m ∧ 0 < δ then m / δ else 1

lemma stepBound_pos (m δ : ℝ) : 0 < stepBound m δ := by
  unfold stepBound
  split_ifs with h
  · exact div_pos h.1 h.2
  · exact one_pos

lemma stepBound_spec {m δ α : ℝ} (hm : 0 ≤ m) (h0 : m = 0 → δ ≤ 0)
    (hα0 : 0 ≤ α) (hα : α ≤ stepBound m δ) : 0 ≤ m - α * δ := by
  unfold stepBound at hα
  split_ifs at hα with h
  · have := (le_div_iff₀ h.2).mp hα
    linarith
  · rcases hm.eq_or_lt with rfl | hmp
    · have hd : δ ≤ 0 := h0 rfl
      nlinarith
    · have hd : δ ≤ 0 := by by_contra hc; push_neg at hc; exact h ⟨hmp, hc⟩
      nlinarith

lemma sum_Over_UBox_of_subset {f : (V → ℤ) → WithTop ℝ} {x y : V → ℝ}
    {S : Finset (V → ℤ)} (hS : S ⊆ UBox f x y) {μ : (V → ℤ) → ℝ}
    (hsupp : ∀ z ∉ S, μ z = 0) (g : (V → ℤ) → ℝ) :
    ∑ z ∈ UBox f x y, μ z * g z = ∑ z ∈ S, μ z * g z := by
  symm
  apply Finset.sum_subset hS
  intro z _ hz
  rw [hsupp z hz, zero_mul]

lemma validShift_to_step {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f)
    {x y : V → ℝ} {rx ry : ℝ}
    (hx : ConvexClosureVal f x = (rx : WithTop ℝ))
    (hy : ConvexClosureVal f y = (ry : WithTop ℝ))
    {μ ν : (V → ℤ) → ℝ}
    (hμ0 : ∀ z, 0 ≤ μ z)
    (hμ_supp : ∀ z ∉ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), μ z = 0)
    (hμ1 : ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), μ z = 1)
    (hμ_mean : ∀ w, ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), μ z * (z w : ℝ) = x w)
    (hμ_val : ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), μ z * (f z).untopD 0 = rx)
    (hν0 : ∀ z, 0 ≤ ν z)
    (hν_supp : ∀ z ∉ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), ν z = 0)
    (hν1 : ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), ν z = 1)
    (hν_mean : ∀ w, ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), ν z * (z w : ℝ) = y w)
    (hν_val : ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), ν z * (f z).untopD 0 = ry)
    {d : V → ℝ} (hvs : ValidShift f x y μ ν d) :
    ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      ConvexClosureVal f (fun w => x w - α * d w) +
        ConvexClosureVal f (fun w => y w + α * d w) ≤
      ConvexClosureVal f x + ConvexClosureVal f y := by
  obtain ⟨δμ, δν, hδμ0, hδν0, hsδμ, hsδν, hmδμ, hmδν, hvδ⟩ := hvs
  set U := UBox f x y
  have hSxU := subset_UBox_left f x y
  have hSyU := subset_UBox_right f x y
  have hUd : ∀ z ∈ U, z ∈ DomZ f := fun z hz => (mem_UBox.mp hz).2
  have hμU_sum : ∑ z ∈ U, μ z = 1 := by
    have := sum_Over_UBox_of_subset hSxU hμ_supp (fun _ => 1)
    simp only [mul_one] at this; rw [this, hμ1]
  have hνU_sum : ∑ z ∈ U, ν z = 1 := by
    have := sum_Over_UBox_of_subset hSyU hν_supp (fun _ => 1)
    simp only [mul_one] at this; rw [this, hν1]
  have hμU_mean : ∀ w, ∑ z ∈ U, μ z * (z w : ℝ) = x w := fun w => by
    rw [sum_Over_UBox_of_subset hSxU hμ_supp, hμ_mean w]
  have hνU_mean : ∀ w, ∑ z ∈ U, ν z * (z w : ℝ) = y w := fun w => by
    rw [sum_Over_UBox_of_subset hSyU hν_supp, hν_mean w]
  have hμU_val : ∑ z ∈ U, μ z * (f z).untopD 0 = rx := by
    rw [sum_Over_UBox_of_subset hSxU hμ_supp, hμ_val]
  have hνU_val : ∑ z ∈ U, ν z * (f z).untopD 0 = ry := by
    rw [sum_Over_UBox_of_subset hSyU hν_supp, hν_val]
  have hU_ne : U.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hμU_sum
    norm_num at hμU_sum
  set α0 : ℝ := U.inf' hU_ne (fun z => min (stepBound (μ z) (δμ z)) (stepBound (ν z) (δν z)))
  have hα0_pos : 0 < α0 := by
    rw [Finset.lt_inf'_iff]
    intro z _
    exact lt_min (stepBound_pos _ _) (stepBound_pos _ _)
  refine ⟨α0, hα0_pos, fun α h0 h1 => ?_⟩
  set lam_x : (V → ℤ) → ℝ := fun z => μ z - α * δμ z
  set lam_y : (V → ℤ) → ℝ := fun z => ν z - α * δν z
  have hlamx0 : ∀ z ∈ U, 0 ≤ lam_x z := by
    intro z hz
    have hle : α ≤ stepBound (μ z) (δμ z) :=
      h1.trans ((Finset.inf'_le _ hz).trans (min_le_left _ _))
    exact stepBound_spec (hμ0 z) (hδμ0 z hz) h0 hle
  have hlamy0 : ∀ z ∈ U, 0 ≤ lam_y z := by
    intro z hz
    have hle : α ≤ stepBound (ν z) (δν z) :=
      h1.trans ((Finset.inf'_le _ hz).trans (min_le_right _ _))
    exact stepBound_spec (hν0 z) (hδν0 z hz) h0 hle
  have hlamx1 : ∑ z ∈ U, lam_x z = 1 := by
    simp only [lam_x, Finset.sum_sub_distrib, ← Finset.mul_sum, hμU_sum, hsδμ]; ring
  have hlamy1 : ∑ z ∈ U, lam_y z = 1 := by
    simp only [lam_y, Finset.sum_sub_distrib, ← Finset.mul_sum, hνU_sum, hsδν]; ring
  have hlamx_mean : ∀ w, ∑ z ∈ U, lam_x z * (z w : ℝ) = x w - α * d w := by
    intro w
    have : ∀ z, (μ z - α * δμ z) * (z w : ℝ) = μ z * (z w : ℝ) - α * (δμ z * (z w : ℝ)) :=
      fun z => by ring
    simp_rw [lam_x, this, Finset.sum_sub_distrib, ← Finset.mul_sum, hμU_mean w, hmδμ w]
  have hlamy_mean : ∀ w, ∑ z ∈ U, lam_y z * (z w : ℝ) = y w + α * d w := by
    intro w
    have : ∀ z, (ν z - α * δν z) * (z w : ℝ) = ν z * (z w : ℝ) - α * (δν z * (z w : ℝ)) :=
      fun z => by ring
    simp_rw [lam_y, this, Finset.sum_sub_distrib, ← Finset.mul_sum, hνU_mean w, hmδν w]; ring
  have hcx := ccv_le_of f hf U (fun w => x w - α * d w) lam_x hlamx0 hlamx1 hUd hlamx_mean
  have hcy := ccv_le_of f hf U (fun w => y w + α * d w) lam_y hlamy0 hlamy1 hUd hlamy_mean
  refine (add_le_add hcx hcy).trans ?_
  rw [hx, hy, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  have ex : ∑ z ∈ U, lam_x z * (f z).untopD 0 = rx - α * ∑ z ∈ U, δμ z * (f z).untopD 0 := by
    have : ∀ z, (μ z - α * δμ z) * (f z).untopD 0 =
        μ z * (f z).untopD 0 - α * (δμ z * (f z).untopD 0) := fun z => by ring
    simp_rw [lam_x, this, Finset.sum_sub_distrib, ← Finset.mul_sum, hμU_val]
  have ey : ∑ z ∈ U, lam_y z * (f z).untopD 0 = ry - α * ∑ z ∈ U, δν z * (f z).untopD 0 := by
    have : ∀ z, (ν z - α * δν z) * (f z).untopD 0 =
        ν z * (f z).untopD 0 - α * (δν z * (f z).untopD 0) := fun z => by ring
    simp_rw [lam_y, this, Finset.sum_sub_distrib, ← Finset.mul_sum, hνU_val]
  rw [ex, ey]
  nlinarith

def ZeroShiftAt (f : (V → ℤ) → WithTop ℝ) (x y : V → ℝ) (μ ν : (V → ℤ) → ℝ) (a : V → ℤ) : Prop :=
  a ∈ UBox f x y ∧
  (∀ w : V, min ⌊x w⌋ ⌊y w⌋ ≤ a w ∧ a w ≤ max ⌈x w⌉ ⌈y w⌉) ∧
  ∃ δμ δν : (V → ℤ) → ℝ,
    (∀ z ∈ UBox f x y, μ z = 0 → δμ z ≤ (if z = a then -1 else 0)) ∧
    (∀ z ∈ UBox f x y, ν z = 0 → δν z ≤ 0) ∧
    (∑ z ∈ UBox f x y, δμ z = 0) ∧
    (∑ z ∈ UBox f x y, δν z = 0) ∧
    (∀ w : V, ∑ z ∈ UBox f x y, δμ z * (z w : ℝ) = 0) ∧
    (∀ w : V, ∑ z ∈ UBox f x y, δν z * (z w : ℝ) = 0) ∧
    0 ≤ ∑ z ∈ UBox f x y, δμ z * (f z).untopD 0 + ∑ z ∈ UBox f x y, δν z * (f z).untopD 0

lemma zeroShiftAt_init {f : (V → ℤ) → WithTop ℝ} {x y : V → ℝ} {μ ν : (V → ℤ) → ℝ}
    {a0 : V → ℤ} (ha0 : a0 ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x))
    (hμa0 : 0 < μ a0) :
    ZeroShiftAt f x y μ ν a0 := by
  have ha0U : a0 ∈ UBox f x y := subset_UBox_left f x y ha0
  rw [Finset.mem_filter, mem_intNbhd] at ha0
  refine ⟨ha0U, fun w => ⟨(min_le_left _ _).trans (ha0.1 w).1, (ha0.1 w).2.trans (le_max_left _ _)⟩,
    fun _ => 0, fun _ => 0, ?_, ?_, by simp, by simp, by simp, by simp, by simp⟩
  · intro z _ hz0
    have hza : z ≠ a0 := by rintro rfl; linarith
    simp [hza]
  · intro _ _ _; exact le_rfl

lemma sum_ite_pair {U : Finset (V → ℤ)} {p q : V → ℤ} (hp : p ∈ U) (hq : q ∈ U)
    (g : (V → ℤ) → ℝ) :
    ∑ z ∈ U, ((if z = p then (1:ℝ) else 0) - (if z = q then (1:ℝ) else 0)) * g z = g p - g q := by
  have : ∀ z, ((if z = p then (1:ℝ) else 0) - (if z = q then (1:ℝ) else 0)) * g z =
      (if z = p then g z else 0) - (if z = q then g z else 0) := by
    intro z; split_ifs <;> ring
  simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', hp, hq, if_true]

lemma zeroShiftAt_validShift_and_step {f : (V → ℤ) → WithTop ℝ} {x y : V → ℝ} {μ ν : (V → ℤ) → ℝ}
    {a b0 : V → ℤ} (ha : ZeroShiftAt f x y μ ν a)
    (hb0 : b0 ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y)) (hνb0 : 0 < ν b0)
    {k v : V} (hk : b0 k < a k) (hv : a v < b0 v)
    (hineq : f (fun w => a w - CharVec k w + CharVec v w) +
      f (fun w => b0 w + CharVec k w - CharVec v w) ≤ f a + f b0) :
    ValidShift f x y μ ν (fun w => (CharVec k w : ℝ) - (CharVec v w : ℝ)) ∧
    (ValidShift f x y μ ν (fun w => (CharVec v w : ℝ) - (CharVec k w : ℝ)) →
      ZeroShiftAt f x y μ ν (fun w => a w - CharVec k w + CharVec v w)) := by
  obtain ⟨haU, habox, δμ, δν, hδμ0, hδν0, hsδμ, hsδν, hmδμ, hmδν, hvδ⟩ := ha
  have hb0U : b0 ∈ UBox f x y := subset_UBox_right f x y hb0
  have ha_dom : f a ≠ ⊤ := (mem_UBox.mp haU).2
  have hb0_dom : f b0 ≠ ⊤ := (mem_UBox.mp hb0U).2
  rw [Finset.mem_filter, mem_intNbhd] at hb0
  have hkv : k ≠ v := by rintro rfl; omega
  set a' : V → ℤ := fun w => a w - CharVec k w + CharVec v w with ha'def
  set b' : V → ℤ := fun w => b0 w + CharVec k w - CharVec v w with hb'def
  have hsum_ne : f a + f b0 ≠ ⊤ := WithTop.add_ne_top.mpr ⟨ha_dom, hb0_dom⟩
  have hsum'_ne : f a' + f b' ≠ ⊤ := ne_top_of_le_ne_top hsum_ne hineq
  obtain ⟨ha'_dom, hb'_dom⟩ := WithTop.add_ne_top.mp hsum'_ne
  have ha'box : ∀ w, min ⌊x w⌋ ⌊y w⌋ ≤ a' w ∧ a' w ≤ max ⌈x w⌉ ⌈y w⌉ := by
    intro w
    have h1 := habox w
    have h2 := hb0.1 w
    have h3 := min_le_right ⌊x w⌋ ⌊y w⌋
    have h4 := le_max_right ⌈x w⌉ ⌈y w⌉
    simp only [ha'def, CharVec]
    split_ifs <;> subst_vars <;> omega
  have ha'U : a' ∈ UBox f x y := by
    rw [mem_UBox]
    exact ⟨fun w => ⟨by have := (ha'box w).1; omega, by have := (ha'box w).2; omega⟩, ha'_dom⟩
  have hb'U : b' ∈ UBox f x y := by
    rw [mem_UBox]
    refine ⟨fun w => ?_, hb'_dom⟩
    have h2 := hb0.1 w
    have h3 := min_le_right ⌊x w⌋ ⌊y w⌋
    have h4 := le_max_right ⌈x w⌉ ⌈y w⌉
    simp only [hb'def, CharVec]
    split_ifs <;> omega
  obtain ⟨ra, hra⟩ := WithTop.ne_top_iff_exists.mp ha_dom
  obtain ⟨rb0, hrb0⟩ := WithTop.ne_top_iff_exists.mp hb0_dom
  obtain ⟨ra', hra'⟩ := WithTop.ne_top_iff_exists.mp ha'_dom
  obtain ⟨rb', hrb'⟩ := WithTop.ne_top_iff_exists.mp hb'_dom
  have hrineq : (f a').untopD 0 + (f b').untopD 0 ≤ (f a).untopD 0 + (f b0).untopD 0 := by
    have h1 : ((ra' + rb' : ℝ) : WithTop ℝ) ≤ ((ra + rb0 : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_add, WithTop.coe_add, hra', hrb', hra, hrb0]; exact hineq
    have h2 := WithTop.coe_le_coe.mp h1
    have ea : (f a).untopD 0 = ra := by rw [← hra]; rfl
    have eb0 : (f b0).untopD 0 = rb0 := by rw [← hrb0]; rfl
    have ea' : (f a').untopD 0 = ra' := by rw [← hra']; rfl
    have eb' : (f b').untopD 0 = rb' := by rw [← hrb']; rfl
    linarith
  set δμ1 : (V → ℤ) → ℝ := fun z => δμ z + ((if z = a then 1 else 0) - (if z = a' then 1 else 0))
  set δν1 : (V → ℤ) → ℝ := fun z => δν z + ((if z = b0 then 1 else 0) - (if z = b' then 1 else 0))
  have hδμ1_bound : ∀ z ∈ UBox f x y, μ z = 0 → δμ1 z ≤ (if z = a' then -1 else 0) := by
    intro z hz h0
    have hbase := hδμ0 z hz h0
    simp only [δμ1]
    split_ifs at hbase ⊢ <;> linarith
  have hδν1_bound : ∀ z ∈ UBox f x y, ν z = 0 → δν1 z ≤ 0 := by
    intro z hz h0
    have hbase := hδν0 z hz h0
    have hzb0 : z ≠ b0 := by rintro rfl; linarith
    simp only [δν1, if_neg hzb0]
    split_ifs <;> linarith
  have hsδμ1 : ∑ z ∈ UBox f x y, δμ1 z = 0 := by
    have := sum_ite_pair haU ha'U (fun _ => 1)
    simp only [mul_one] at this
    simp only [δμ1, Finset.sum_add_distrib, hsδμ, this]; ring
  have hsδν1 : ∑ z ∈ UBox f x y, δν1 z = 0 := by
    have := sum_ite_pair hb0U hb'U (fun _ => 1)
    simp only [mul_one] at this
    simp only [δν1, Finset.sum_add_distrib, hsδν, this]; ring
  have hmδμ1 : ∀ w : V, ∑ z ∈ UBox f x y, δμ1 z * (z w : ℝ) = (CharVec k w : ℝ) - (CharVec v w : ℝ) := by
    intro w
    have e : ∀ z, δμ1 z * (z w : ℝ) = δμ z * (z w : ℝ) +
        ((if z = a then 1 else 0) - (if z = a' then 1 else 0)) * (z w : ℝ) := fun z => add_mul _ _ _
    simp_rw [e, Finset.sum_add_distrib, hmδμ w, sum_ite_pair haU ha'U (fun z => (z w : ℝ)), ha'def]
    push_cast; ring
  have hmδν1 : ∀ w : V, ∑ z ∈ UBox f x y, δν1 z * (z w : ℝ) = -((CharVec k w : ℝ) - (CharVec v w : ℝ)) := by
    intro w
    have e : ∀ z, δν1 z * (z w : ℝ) = δν z * (z w : ℝ) +
        ((if z = b0 then 1 else 0) - (if z = b' then 1 else 0)) * (z w : ℝ) := fun z => add_mul _ _ _
    simp_rw [e, Finset.sum_add_distrib, hmδν w, sum_ite_pair hb0U hb'U (fun z => (z w : ℝ)), hb'def]
    push_cast; ring
  have hvδ1 : 0 ≤ ∑ z ∈ UBox f x y, δμ1 z * (f z).untopD 0 + ∑ z ∈ UBox f x y, δν1 z * (f z).untopD 0 := by
    have e1 : ∀ z, δμ1 z * (f z).untopD 0 = δμ z * (f z).untopD 0 +
        ((if z = a then 1 else 0) - (if z = a' then 1 else 0)) * (f z).untopD 0 := fun z => add_mul _ _ _
    have e2 : ∀ z, δν1 z * (f z).untopD 0 = δν z * (f z).untopD 0 +
        ((if z = b0 then 1 else 0) - (if z = b' then 1 else 0)) * (f z).untopD 0 := fun z => add_mul _ _ _
    simp_rw [e1, e2, Finset.sum_add_distrib, sum_ite_pair haU ha'U, sum_ite_pair hb0U hb'U]
    linarith
  refine ⟨⟨δμ1, δν1, fun z hz h0 => (hδμ1_bound z hz h0).trans (by split_ifs <;> norm_num),
    hδν1_bound, hsδμ1, hsδν1, hmδμ1, hmδν1, hvδ1⟩, ?_⟩
  rintro ⟨δμ2, δν2, hδμ2, hδν2, hsδμ2, hsδν2, hmδμ2, hmδν2, hvδ2⟩
  refine ⟨ha'U, ha'box, fun z => δμ1 z + δμ2 z, fun z => δν1 z + δν2 z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz h0; linarith [hδμ1_bound z hz h0, hδμ2 z hz h0]
  · intro z hz h0; linarith [hδν1_bound z hz h0, hδν2 z hz h0]
  · rw [Finset.sum_add_distrib, hsδμ1, hsδμ2, add_zero]
  · rw [Finset.sum_add_distrib, hsδν1, hsδν2, add_zero]
  · intro w
    have : ∀ z, (δμ1 z + δμ2 z) * (z w : ℝ) = δμ1 z * (z w : ℝ) + δμ2 z * (z w : ℝ) :=
      fun z => add_mul _ _ _
    simp_rw [this, Finset.sum_add_distrib, hmδμ1 w, hmδμ2 w]; ring
  · intro w
    have : ∀ z, (δν1 z + δν2 z) * (z w : ℝ) = δν1 z * (z w : ℝ) + δν2 z * (z w : ℝ) :=
      fun z => add_mul _ _ _
    simp_rw [this, Finset.sum_add_distrib, hmδν1 w, hmδν2 w]; ring
  · have e1 : ∀ z, (δμ1 z + δμ2 z) * (f z).untopD 0 =
        δμ1 z * (f z).untopD 0 + δμ2 z * (f z).untopD 0 := fun z => add_mul _ _ _
    have e2 : ∀ z, (δν1 z + δν2 z) * (f z).untopD 0 =
        δν1 z * (f z).untopD 0 + δν2 z * (f z).untopD 0 := fun z => add_mul _ _ _
    simp_rw [e1, e2, Finset.sum_add_distrib]
    linarith

/-! ### Part 3: Graph reachability and SCC induction -/

lemma exists_pos_pair {S : Finset (V → ℤ)} {μ : (V → ℤ) → ℝ}
    (hμ0 : ∀ z ∈ S, 0 ≤ μ z) (hμ1 : ∑ z ∈ S, μ z = 1)
    {g : (V → ℤ) → ℝ} {c : ℝ} (hgt : c < ∑ z ∈ S, μ z * g z) :
    ∃ z ∈ S, 0 < μ z ∧ c < g z := by
  by_contra hcon
  push_neg at hcon
  have hle : ∑ z ∈ S, μ z * g z ≤ ∑ z ∈ S, μ z * c := by
    apply Finset.sum_le_sum
    intro z hz
    rcases (hμ0 z hz).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · exact mul_le_mul_of_nonneg_left (hcon z hz hpos) (hμ0 z hz)
  rw [← Finset.sum_mul, hμ1, one_mul] at hle
  linarith

lemma exists_lt_pair {S : Finset (V → ℤ)} {μ : (V → ℤ) → ℝ}
    (hμ0 : ∀ z ∈ S, 0 ≤ μ z) (hμ1 : ∑ z ∈ S, μ z = 1)
    {g : (V → ℤ) → ℝ} {c : ℝ} (hlt : ∑ z ∈ S, μ z * g z < c) :
    ∃ z ∈ S, 0 < μ z ∧ g z < c := by
  by_contra hcon
  push_neg at hcon
  have hle : ∑ z ∈ S, μ z * c ≤ ∑ z ∈ S, μ z * g z := by
    apply Finset.sum_le_sum
    intro z hz
    rcases (hμ0 z hz).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · exact mul_le_mul_of_nonneg_left (hcon z hz hpos) (hμ0 z hz)
  rw [← Finset.sum_mul, hμ1, one_mul] at hle
  linarith

lemma active_of_reach_lt {f : (V → ℤ) → WithTop ℝ} {x y : V → ℝ} {μ ν : (V → ℤ) → ℝ}
    (hμ0 : ∀ z, 0 ≤ μ z)
    (hμ1 : ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), μ z = 1)
    (hμ_mean : ∀ w, ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), μ z * (z w : ℝ) = x w)
    (hν0 : ∀ z, 0 ≤ ν z)
    (hν1 : ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), ν z = 1)
    (hν_mean : ∀ w, ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), ν z * (z w : ℝ) = y w)
    {v : V} (hyx : y v ≤ x v)
    {a0 b0 : V → ℤ}
    (ha0 : a0 ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x))
    (hb0 : b0 ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y))
    (hab : a0 v < b0 v) :
    ∃ a ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), 0 < μ a ∧
      ∃ b ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), 0 < ν b ∧ b v < a v := by
  set Sx := Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x)
  set Sy := Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y)
  have ha0_nb := (mem_intNbhd.mp (Finset.mem_filter.mp ha0).1) v
  have hb0_nb := (mem_intNbhd.mp (Finset.mem_filter.mp hb0).1) v
  have hfl_lt_ce : ⌊x v⌋ + 1 ≤ ⌈y v⌉ := by omega
  have hce_le : ⌈y v⌉ ≤ ⌊x v⌋ + 1 := by
    apply Int.ceil_le.mpr
    push_cast
    linarith [Int.lt_floor_add_one (x v)]
  have hce_eq : ⌈y v⌉ = ⌊x v⌋ + 1 := le_antisymm hce_le hfl_lt_ce
  have hfl_lt_x : (⌊x v⌋ : ℝ) < x v := by
    by_contra h
    push_neg at h
    have hx_eq : x v = (⌊x v⌋ : ℝ) := le_antisymm h (Int.floor_le (x v))
    have hy_le : y v ≤ (⌊x v⌋ : ℝ) := hyx.trans_eq hx_eq
    have : ⌈y v⌉ ≤ ⌊x v⌋ := Int.ceil_le.mpr hy_le
    omega
  have hy_lt_ce : y v < (⌈y v⌉ : ℝ) := by
    by_contra h
    push_neg at h
    have hy_eq : y v = (⌈y v⌉ : ℝ) := le_antisymm (Int.le_ceil (y v)) h
    have : ((⌊x v⌋ + 1 : ℤ) : ℝ) ≤ x v := by
      calc ((⌊x v⌋ + 1 : ℤ) : ℝ) = (⌈y v⌉ : ℝ) := by exact_mod_cast hce_eq.symm
        _ = y v := hy_eq.symm
        _ ≤ x v := hyx
    push_cast at this
    linarith [Int.lt_floor_add_one (x v)]
  obtain ⟨a, haSx, hμa, ha_gt⟩ := exists_pos_pair (fun z _ => hμ0 z) hμ1
    (by rw [hμ_mean v]; exact hfl_lt_x)
  obtain ⟨b, hbSy, hνb, hb_lt⟩ := exists_lt_pair (fun z _ => hν0 z) hν1
    (by rw [hν_mean v]; exact hy_lt_ce)
  have ha_ge : ⌊x v⌋ + 1 ≤ a v := by
    have : ⌊x v⌋ < a v := by exact_mod_cast ha_gt
    omega
  have hb_le : b v ≤ ⌈y v⌉ - 1 := by
    have : b v < ⌈y v⌉ := by exact_mod_cast hb_lt
    omega
  exact ⟨a, haSx, hμa, b, hbSy, hνb, by omega⟩

lemma eq_of_forall_le_and_sum_le {f : (V → ℤ) → WithTop ℝ} {x y : V → ℝ} {μ ν : (V → ℤ) → ℝ}
    (hμ0 : ∀ z, 0 ≤ μ z)
    (hμ1 : ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), μ z = 1)
    (hμ_mean : ∀ w, ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), μ z * (z w : ℝ) = x w)
    (hν0 : ∀ z, 0 ≤ ν z)
    (hν1 : ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), ν z = 1)
    (hν_mean : ∀ w, ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), ν z * (z w : ℝ) = y w)
    {C : Finset V} (hyx : ∀ m ∈ C, y m ≤ x m)
    (hle : ∀ a0 ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), 0 < μ a0 →
      ∀ b0 ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), 0 < ν b0 →
        ∑ m ∈ C, a0 m ≤ ∑ m ∈ C, b0 m) :
    (∀ m ∈ C, x m = y m) ∧
    (∀ a0 ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), 0 < μ a0 →
      ∀ b0 ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), 0 < ν b0 →
        ∑ m ∈ C, a0 m = ∑ m ∈ C, b0 m) := by
  set Sx := Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x)
  set Sy := Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y)
  have hmean_x : ∑ a ∈ Sx, μ a * ((∑ m ∈ C, a m : ℤ) : ℝ) = ∑ m ∈ C, x m := by
    calc ∑ a ∈ Sx, μ a * ((∑ m ∈ C, a m : ℤ) : ℝ)
        = ∑ a ∈ Sx, ∑ m ∈ C, μ a * (a m : ℝ) := by
          apply Finset.sum_congr rfl; intro a _; push_cast; rw [Finset.mul_sum]
      _ = ∑ m ∈ C, ∑ a ∈ Sx, μ a * (a m : ℝ) := Finset.sum_comm
      _ = ∑ m ∈ C, x m := Finset.sum_congr rfl (fun m _ => hμ_mean m)
  have hmean_y : ∑ b ∈ Sy, ν b * ((∑ m ∈ C, b m : ℤ) : ℝ) = ∑ m ∈ C, y m := by
    calc ∑ b ∈ Sy, ν b * ((∑ m ∈ C, b m : ℤ) : ℝ)
        = ∑ b ∈ Sy, ∑ m ∈ C, ν b * (b m : ℝ) := by
          apply Finset.sum_congr rfl; intro b _; push_cast; rw [Finset.mul_sum]
      _ = ∑ m ∈ C, ∑ b ∈ Sy, ν b * (b m : ℝ) := Finset.sum_comm
      _ = ∑ m ∈ C, y m := Finset.sum_congr rfl (fun m _ => hν_mean m)
  have hterm_nn : ∀ p ∈ Sx ×ˢ Sy,
      0 ≤ μ p.1 * ν p.2 * (((∑ m ∈ C, p.2 m : ℤ) : ℝ) - ((∑ m ∈ C, p.1 m : ℤ) : ℝ)) := by
    rintro ⟨a, b⟩ hp
    rw [Finset.mem_product] at hp
    rcases (hμ0 a).eq_or_lt with ha0 | hapos
    · rw [← ha0]; simp
    · rcases (hν0 b).eq_or_lt with hb0 | hbpos
      · rw [← hb0]; simp
      · have hab : ((∑ m ∈ C, a m : ℤ) : ℝ) ≤ ((∑ m ∈ C, b m : ℤ) : ℝ) := by
          exact_mod_cast hle a hp.1 hapos b hp.2 hbpos
        exact mul_nonneg (mul_nonneg (hμ0 a) (hν0 b)) (sub_nonneg.mpr hab)
  have hprod_sum : ∑ p ∈ Sx ×ˢ Sy,
      μ p.1 * ν p.2 * (((∑ m ∈ C, p.2 m : ℤ) : ℝ) - ((∑ m ∈ C, p.1 m : ℤ) : ℝ)) =
      (∑ m ∈ C, y m) - (∑ m ∈ C, x m) := by
    rw [Finset.sum_product]
    have : ∀ a ∈ Sx, ∑ b ∈ Sy, μ a * ν b * (((∑ m ∈ C, b m : ℤ) : ℝ) - ((∑ m ∈ C, a m : ℤ) : ℝ)) =
        μ a * (∑ m ∈ C, y m) - (μ a * ((∑ m ∈ C, a m : ℤ) : ℝ)) * (∑ b ∈ Sy, ν b) := by
      intro a _
      have e : ∀ b, μ a * ν b * (((∑ m ∈ C, b m : ℤ) : ℝ) - ((∑ m ∈ C, a m : ℤ) : ℝ)) =
          μ a * (ν b * ((∑ m ∈ C, b m : ℤ) : ℝ)) - (μ a * ((∑ m ∈ C, a m : ℤ) : ℝ)) * ν b :=
        fun b => by ring
      simp_rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum, hmean_y]
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ1, one_mul]
    simp_rw [hν1, mul_one, hmean_x]
  have hsum_nn : 0 ≤ (∑ m ∈ C, y m) - (∑ m ∈ C, x m) := by
    rw [← hprod_sum]; exact Finset.sum_nonneg hterm_nn
  have hsum_np : (∑ m ∈ C, y m) - (∑ m ∈ C, x m) ≤ 0 := by
    linarith [Finset.sum_le_sum hyx]
  have hsum_eq : ∑ m ∈ C, y m = ∑ m ∈ C, x m := by linarith
  have hprod_zero : ∑ p ∈ Sx ×ˢ Sy,
      μ p.1 * ν p.2 * (((∑ m ∈ C, p.2 m : ℤ) : ℝ) - ((∑ m ∈ C, p.1 m : ℤ) : ℝ)) = 0 := by
    rw [hprod_sum, hsum_eq, sub_self]
  refine ⟨fun m hm => ((Finset.sum_eq_sum_iff_of_le hyx).mp hsum_eq m hm).symm, ?_⟩
  intro a0 ha0 hμa0 b0 hb0 hνb0
  have hp := (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).mp hprod_zero
    (a0, b0) (Finset.mem_product.mpr ⟨ha0, hb0⟩)
  have hpos : 0 < μ a0 * ν b0 := mul_pos hμa0 hνb0
  have hsub : ((∑ m ∈ C, b0 m : ℤ) : ℝ) - ((∑ m ∈ C, a0 m : ℤ) : ℝ) = 0 := by
    rcases mul_eq_zero.mp hp with h1 | h2
    · linarith
    · exact h2
  have : ((∑ m ∈ C, a0 m : ℤ) : ℝ) = ((∑ m ∈ C, b0 m : ℤ) : ℝ) := by linarith
  exact_mod_cast this

lemma step_dist_lt (a b0 : V → ℤ) (k v : V) (hk : b0 k < a k) (hv : a v < b0 v) :
    (∑ w, |(a w - CharVec k w + CharVec v w) - b0 w|).toNat <
      (∑ w, |a w - b0 w|).toNat := by
  have hkv : k ≠ v := by rintro rfl; omega
  set a' : V → ℤ := fun w => a w - CharVec k w + CharVec v w
  have hp : ∀ w : V, |a' w - b0 w| = |a w - b0 w| -
      (if w = k then 1 else 0) - (if w = v then 1 else 0) := by
    intro w
    by_cases hwk : w = k
    · subst w
      simp only [a', CharVec, if_true, if_neg hkv, add_zero]
      rw [abs_of_nonneg (by omega : 0 ≤ a k - 1 - b0 k), abs_of_pos (by omega : 0 < a k - b0 k)]
      omega
    · by_cases hwv : w = v
      · subst w
        simp only [a', CharVec, if_true, if_neg (Ne.symm hkv), sub_zero]
        rw [abs_of_nonpos (by omega : a v + 1 - b0 v ≤ 0), abs_of_neg (by omega : a v - b0 v < 0)]
        omega
      · simp [a', CharVec, hwk, hwv]
  have hdiff : (∑ w, |a' w - b0 w|) = (∑ w, |a w - b0 w|) - 2 := by
    simp_rw [hp, Finset.sum_sub_distrib]
    simp; ring
  change (∑ w, |a' w - b0 w|).toNat < (∑ w, |a w - b0 w|).toNat
  have hn : 0 ≤ ∑ w, |a' w - b0 w| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (Int.toNat_lt_toNat (by omega : 0 < ∑ w, |a w - b0 w|)).mpr
  omega

theorem scc_chain_step {f : (V → ℤ) → WithTop ℝ} (hf : MExchangeAxiom f)
    {x y : V → ℝ} {μ ν : (V → ℤ) → ℝ}
    (hμ0 : ∀ z, 0 ≤ μ z)
    (hμ1 : ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), μ z = 1)
    (hμ_mean : ∀ w, ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), μ z * (z w : ℝ) = x w)
    (hν0 : ∀ z, 0 ≤ ν z)
    (hν1 : ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), ν z = 1)
    (hν_mean : ∀ w, ∑ z ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), ν z * (z w : ℝ) = y w)
    {u : V}
    (hno_neg : ∀ v : V, ValidShift f x y μ ν (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ)) → y v ≤ x v)
    (Active : Finset V)
    (hActive_def : Active = Finset.univ.filter (fun k : V =>
      ValidShift f x y μ ν (fun w => (CharVec u w : ℝ) - (CharVec k w : ℝ)) ∧
      ∃ a ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x), 0 < μ a ∧
      ∃ b ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y), 0 < ν b ∧ b k < a k))
    {D C : Finset V} (hCD : Disjoint D C) (hCA : C ⊆ Active)
    (hCsink : ∀ k ∈ C, ∀ v ∈ Active \ D,
      ValidShift f x y μ ν (fun w => (CharVec k w : ℝ) - (CharVec v w : ℝ)) → v ∈ C)
    (hCsc : ∀ v ∈ C, ∀ k ∈ C,
      ValidShift f x y μ ν (fun w => (CharVec v w : ℝ) - (CharVec k w : ℝ)))
    {a0 b0 : V → ℤ}
    (ha0 : a0 ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x))
    (hb0 : b0 ∈ Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y)) (hνb0 : 0 < ν b0) :
    ∀ n : ℕ, ∀ a : V → ℤ, (∑ w, |a w - b0 w|).toNat ≤ n →
      ZeroShiftAt f x y μ ν a →
      (∀ m ∈ D, a m = b0 m) →
      (∀ m ∉ D ∪ C, a m = a0 m) →
      (∑ m ∈ C, a m = ∑ m ∈ C, a0 m) →
      ∃ a' : V → ℤ, ZeroShiftAt f x y μ ν a' ∧
        (∀ m ∈ D, a' m = b0 m) ∧
        (∀ m ∉ D ∪ C, a' m = a0 m) ∧
        (∀ m ∈ C, a' m ≤ b0 m) ∧
        (∑ m ∈ C, a' m = ∑ m ∈ C, a0 m) := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro a hn hza haD haOut haSum
  by_cases hdone : ∀ m ∈ C, a m ≤ b0 m
  · exact ⟨a, hza, haD, haOut, hdone, haSum⟩
  · push_neg at hdone
    obtain ⟨k, hkC, hklt⟩ := hdone
    have ha_dom : a ∈ DomZ f := (mem_UBox.mp hza.1).2
    have hb0_dom : b0 ∈ DomZ f := (Finset.mem_filter.mp hb0).2
    obtain ⟨v, hv, hineq⟩ := hf a ha_dom b0 hb0_dom k (by simp [SuppPos, hklt])
    simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hstep := zeroShiftAt_validShift_and_step hza hb0 hνb0 hklt hv hineq
    have hEkv : ValidShift f x y μ ν (fun w => (CharVec k w : ℝ) - (CharVec v w : ℝ)) := hstep.1
    have hkAct : k ∈ Active := hCA hkC
    have hkReach : ValidShift f x y μ ν (fun w => (CharVec u w : ℝ) - (CharVec k w : ℝ)) := by
      rw [hActive_def, Finset.mem_filter] at hkAct; exact hkAct.2.1
    have hvReach : ValidShift f x y μ ν (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ)) := by
      have := validShift_add hkReach hEkv
      convert this using 1; funext w; ring
    have hv_notD : v ∉ D := by
      intro hvD; have := haD v hvD; omega
    have hvC : v ∈ C := by
      by_contra hv_notC
      have hv_notDC : v ∉ D ∪ C := by simp [hv_notD, hv_notC]
      have ha0v : a0 v < b0 v := by rw [← haOut v hv_notDC]; exact hv
      have hvAct : v ∈ Active := by
        rw [hActive_def, Finset.mem_filter]
        refine ⟨Finset.mem_univ v, hvReach, ?_⟩
        exact active_of_reach_lt hμ0 hμ1 hμ_mean hν0 hν1 hν_mean (hno_neg v hvReach) ha0 hb0 ha0v
      exact hv_notC (hCsink k hkC v (Finset.mem_sdiff.mpr ⟨hvAct, hv_notD⟩) hEkv)
    have hEvk := hCsc v hvC k hkC
    set a1 : V → ℤ := fun w => a w - CharVec k w + CharVec v w
    have hza1 : ZeroShiftAt f x y μ ν a1 := hstep.2 hEvk
    have hkv : k ≠ v := by rintro rfl; omega
    have ha1D : ∀ m ∈ D, a1 m = b0 m := by
      intro m hm
      have hmk : m ≠ k := fun h => Finset.disjoint_left.mp hCD hm (h ▸ hkC)
      have hmv : m ≠ v := fun h => hv_notD (h ▸ hm)
      simp [a1, CharVec, hmk, hmv, haD m hm]
    have ha1Out : ∀ m ∉ D ∪ C, a1 m = a0 m := by
      intro m hm
      have hmk : m ≠ k := fun h => hm (Finset.mem_union_right D (h ▸ hkC))
      have hmv : m ≠ v := fun h => hm (Finset.mem_union_right D (h ▸ hvC))
      simp [a1, CharVec, hmk, hmv, haOut m hm]
    have ha1Sum : ∑ m ∈ C, a1 m = ∑ m ∈ C, a0 m := by
      have : ∑ m ∈ C, a1 m = ∑ m ∈ C, a m -
          ∑ m ∈ C, CharVec k m + ∑ m ∈ C, CharVec v m := by
        simp only [a1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hk_sum : ∑ m ∈ C, CharVec k m = 1 := by
        simp [CharVec, Finset.sum_ite_eq', hkC]
      have hv_sum : ∑ m ∈ C, CharVec v m = 1 := by
        simp [CharVec, Finset.sum_ite_eq', hvC]
      rw [this, hk_sum, hv_sum, haSum]; ring
    have hlt := step_dist_lt a b0 k v hklt hv
    exact ih ((∑ w, |a1 w - b0 w|).toNat) (lt_of_lt_of_le hlt hn) a1 le_rfl hza1 ha1D ha1Out ha1Sum

theorem main_proof (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) :
    MExchangeAxiomR (ConvexClosureVal f) := by
  intro x hx y hy u hu
  simp only [SuppPosR, Set.mem_setOf_eq] at hu
  obtain ⟨rx, hrx⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨ry, hry⟩ := WithTop.ne_top_iff_exists.mp hy
  have hrx' : ConvexClosureVal f x = (rx : WithTop ℝ) := hrx.symm
  have hry' : ConvexClosureVal f y = (ry : WithTop ℝ) := hry.symm
  obtain ⟨μ, hμ0, hμ_supp, hμ1, hμ_mean, hμ_val⟩ := exists_opt_rep f hf x rx hrx'
  obtain ⟨ν, hν0, hν_supp, hν1, hν_mean, hν_val⟩ := exists_opt_rep f hf y ry hry'
  set Sx := Finset.filter (fun z => z ∈ DomZ f) (IntNbhd x)
  set Sy := Finset.filter (fun z => z ∈ DomZ f) (IntNbhd y)
  by_contra hcon
  push_neg at hcon
  have hno_neg : ∀ v : V, ValidShift f x y μ ν (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ)) → y v ≤ x v := by
    intro v hvs
    by_contra hlt
    push_neg at hlt
    obtain ⟨α0, hα0, hstep⟩ := validShift_to_step hf hrx' hry' hμ0 hμ_supp hμ1 hμ_mean hμ_val
      hν0 hν_supp hν1 hν_mean hν_val hvs
    obtain ⟨α, hα0', hα1, hgt⟩ := hcon v (by simpa [SuppNegR] using hlt) α0 hα0
    exact not_le_of_gt hgt (hstep α hα0' hα1)
  set E : V → V → Prop := fun k v => ValidShift f x y μ ν (fun w => (CharVec k w : ℝ) - (CharVec v w : ℝ))
  have E_refl : ∀ k : V, E k k := by
    intro k; show ValidShift f x y μ ν _
    have := validShift_zero f x y μ ν
    convert this using 1; funext w; simp
  have E_trans : ∀ {k m v : V}, E k m → E m v → E k v := by
    intro k m v h1 h2
    have := validShift_add h1 h2
    convert this using 1; funext w; ring
  set Active : Finset V := Finset.univ.filter (fun k : V =>
    E u k ∧ ∃ a ∈ Sx, 0 < μ a ∧ ∃ b ∈ Sy, 0 < ν b ∧ b k < a k) with hActive_def
  have hu_active : u ∈ Active := by
    rw [hActive_def, Finset.mem_filter]
    refine ⟨Finset.mem_univ u, E_refl u, ?_⟩
    by_contra hno
    push_neg at hno
    have hprod : ∑ a ∈ Sx, ∑ b ∈ Sy, μ a * ν b * ((a u : ℝ) - (b u : ℝ)) ≤ 0 := by
      apply Finset.sum_nonpos; intro a ha
      apply Finset.sum_nonpos; intro b hb
      rcases (hμ0 a).eq_or_lt with ha0 | hapos
      · rw [← ha0]; simp
      · rcases (hν0 b).eq_or_lt with hb0 | hbpos
        · rw [← hb0]; simp
        · have hab : (a u : ℝ) ≤ (b u : ℝ) := by exact_mod_cast hno a ha hapos b hb hbpos
          exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hμ0 a) (hν0 b)) (sub_nonpos.mpr hab)
    have hprod_eq : ∑ a ∈ Sx, ∑ b ∈ Sy, μ a * ν b * ((a u : ℝ) - (b u : ℝ)) = x u - y u := by
      have : ∀ a ∈ Sx, ∑ b ∈ Sy, μ a * ν b * ((a u : ℝ) - (b u : ℝ)) =
          (μ a * (a u : ℝ)) * (∑ b ∈ Sy, ν b) - μ a * (∑ b ∈ Sy, ν b * (b u : ℝ)) := by
        intro a _
        have e : ∀ b, μ a * ν b * ((a u : ℝ) - (b u : ℝ)) =
            (μ a * (a u : ℝ)) * ν b - μ a * (ν b * (b u : ℝ)) := fun b => by ring
        simp_rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
      simp_rw [hν1, mul_one, hν_mean u, ← Finset.sum_mul, hμ1, one_mul, hμ_mean u]
    linarith
  suffices H : ∀ n : ℕ, ∀ D : Finset V, (Active \ D).card = n →
      (∀ k ∈ D, ∀ v ∈ Active, E k v → v ∈ D) →
      (∀ m ∈ D, x m = y m) →
      (∀ a0 ∈ Sx, 0 < μ a0 → ∀ b0 ∈ Sy, 0 < ν b0 →
        ∃ a : V → ℤ, ZeroShiftAt f x y μ ν a ∧ (∀ m ∈ D, a m = b0 m) ∧ (∀ m ∉ D, a m = a0 m)) →
      False by
    exact H (Active \ ∅).card ∅ rfl (by simp) (by simp)
      (fun a0 ha0 hμa0 _ _ _ => ⟨a0, zeroShiftAt_init ha0 hμa0, by simp, by simp⟩)
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro D hcard hDclosed hDxy hDchain
  by_cases hne : (Active \ D).Nonempty
  · obtain ⟨kstar, hkstar, hkmin⟩ := (Active \ D).exists_min_image
      (fun k => ((Active \ D).filter (fun v => E k v)).card) hne
    set C : Finset V := (Active \ D).filter (fun v => E kstar v) with hCdef
    have hkstarC : kstar ∈ C := by simp [hCdef, hkstar, E_refl kstar]
    have hC_sub_sdiff : C ⊆ Active \ D := Finset.filter_subset _ _
    have hCA : C ⊆ Active := hC_sub_sdiff.trans Finset.sdiff_subset
    have hCD : Disjoint D C := by
      rw [Finset.disjoint_left]
      intro m hmD hmC
      exact (Finset.mem_sdiff.mp (hC_sub_sdiff hmC)).2 hmD
    have hCsink : ∀ k ∈ C, ∀ v ∈ Active \ D, E k v → v ∈ C := by
      intro k hkC v hv hkv
      rw [hCdef, Finset.mem_filter] at hkC ⊢
      exact ⟨hv, E_trans hkC.2 hkv⟩
    have hCsc : ∀ v ∈ C, ∀ k ∈ C, E v k := by
      intro v hvC k hkC
      set Cv : Finset V := (Active \ D).filter (fun w => E v w)
      have hCv_sub : Cv ⊆ C := by
        intro w hw
        rw [Finset.mem_filter] at hw
        exact hCsink v hvC w hw.1 hw.2
      have hCv_le : C.card ≤ Cv.card := hkmin v (hC_sub_sdiff hvC)
      have hCv_eq : Cv = C := Finset.eq_of_subset_of_card_le hCv_sub hCv_le
      have hkCv : k ∈ Cv := hCv_eq.symm ▸ hkC
      exact (Finset.mem_filter.mp hkCv).2
    have hstep_all : ∀ a0 ∈ Sx, 0 < μ a0 → ∀ b0 ∈ Sy, 0 < ν b0 →
        ∃ a' : V → ℤ, ZeroShiftAt f x y μ ν a' ∧
          (∀ m ∈ D, a' m = b0 m) ∧
          (∀ m ∉ D ∪ C, a' m = a0 m) ∧
          (∀ m ∈ C, a' m ≤ b0 m) ∧
          (∑ m ∈ C, a' m = ∑ m ∈ C, a0 m) := by
      intro a0 ha0 hμa0 b0 hb0 hνb0
      obtain ⟨a1, hza1, ha1D, ha1Out⟩ := hDchain a0 ha0 hμa0 b0 hb0 hνb0
      have ha1Out' : ∀ m ∉ D ∪ C, a1 m = a0 m :=
        fun m hm => ha1Out m (fun hmD => hm (Finset.mem_union_left C hmD))
      have ha1Sum : ∑ m ∈ C, a1 m = ∑ m ∈ C, a0 m := by
        apply Finset.sum_congr rfl
        intro m hmC
        exact ha1Out m (Finset.disjoint_right.mp hCD hmC)
      exact scc_chain_step hf hμ0 hμ1 hμ_mean hν0 hν1 hν_mean hno_neg Active hActive_def
        hCD hCA hCsink hCsc ha0 hb0 hνb0 ((∑ w, |a1 w - b0 w|).toNat) a1 le_rfl hza1 ha1D ha1Out' ha1Sum
    have hle_sum : ∀ a0 ∈ Sx, 0 < μ a0 → ∀ b0 ∈ Sy, 0 < ν b0 →
        ∑ m ∈ C, a0 m ≤ ∑ m ∈ C, b0 m := by
      intro a0 ha0 hμa0 b0 hb0 hνb0
      obtain ⟨a', -, -, -, ha'le, ha'sum⟩ := hstep_all a0 ha0 hμa0 b0 hb0 hνb0
      rw [← ha'sum]
      exact Finset.sum_le_sum ha'le
    have hyxC : ∀ m ∈ C, y m ≤ x m := by
      intro m hmC
      have hmAct := hCA hmC
      rw [hActive_def, Finset.mem_filter] at hmAct
      exact hno_neg m hmAct.2.1
    obtain ⟨hCxy, hCsum_eq⟩ := eq_of_forall_le_and_sum_le hμ0 hμ1 hμ_mean hν0 hν1 hν_mean hyxC hle_sum
    have hDC_closed : ∀ k ∈ D ∪ C, ∀ v ∈ Active, E k v → v ∈ D ∪ C := by
      intro k hk v hvAct hkv
      by_cases hvD : v ∈ D
      · exact Finset.mem_union_left C hvD
      · rcases Finset.mem_union.mp hk with hkD | hkC
        · exact absurd (hDclosed k hkD v hvAct hkv) hvD
        · exact Finset.mem_union_right D (hCsink k hkC v (Finset.mem_sdiff.mpr ⟨hvAct, hvD⟩) hkv)
    have hDC_xy : ∀ m ∈ D ∪ C, x m = y m := by
      intro m hm
      rcases Finset.mem_union.mp hm with hmD | hmC
      · exact hDxy m hmD
      · exact hCxy m hmC
    have hDC_chain : ∀ a0 ∈ Sx, 0 < μ a0 → ∀ b0 ∈ Sy, 0 < ν b0 →
        ∃ a' : V → ℤ, ZeroShiftAt f x y μ ν a' ∧
          (∀ m ∈ D ∪ C, a' m = b0 m) ∧ (∀ m ∉ D ∪ C, a' m = a0 m) := by
      intro a0 ha0 hμa0 b0 hb0 hνb0
      obtain ⟨a', hza', ha'D, ha'Out, ha'le, ha'sum⟩ := hstep_all a0 ha0 hμa0 b0 hb0 hνb0
      have hsum_eq : ∑ m ∈ C, a' m = ∑ m ∈ C, b0 m := ha'sum.trans (hCsum_eq a0 ha0 hμa0 b0 hb0 hνb0)
      have ha'C : ∀ m ∈ C, a' m = b0 m :=
        (Finset.sum_eq_sum_iff_of_le ha'le).mp hsum_eq
      refine ⟨a', hza', ?_, ha'Out⟩
      intro m hm
      rcases Finset.mem_union.mp hm with hmD | hmC
      · exact ha'D m hmD
      · exact ha'C m hmC
    have hcard_lt : (Active \ (D ∪ C)).card < n := by
      rw [← hcard]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.sdiff_subset_sdiff le_rfl Finset.subset_union_left, ?_⟩
      intro heq
      have hk1 : kstar ∈ Active \ D := hkstar
      have hk2 : kstar ∉ Active \ (D ∪ C) := by
        simp [Finset.mem_sdiff, hkstarC]
      exact hk2 (heq ▸ hk1)
    exact ih (Active \ (D ∪ C)).card hcard_lt (D ∪ C) rfl hDC_closed hDC_xy hDC_chain
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
    have := hDxy u (hne hu_active)
    linarith

end MConvexExtPoly

open DiscreteConvex.MConvexFunctionsC

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (_hpoly : IsPolyhedralConvex (ConvexClosureVal f)) :
    MExchangeAxiomR (ConvexClosureVal f) :=
  MConvexExtPoly.main_proof f hf

