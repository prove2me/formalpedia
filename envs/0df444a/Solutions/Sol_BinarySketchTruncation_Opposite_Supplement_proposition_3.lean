-- Prove2me | solution 1 for BinarySketchTruncation.Opposite.Supplement.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:50:30.879723+00:00
-- url     : https://prove2.me/submissions/3341c255-83b3-4f89-80f4-90dfa84f4f59

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Model

section
namespace BinarySketchTruncation.Dev.Prop3
open BinarySketchTruncation.Opposite

lemma twoByTwo (x0 x1 x0' x1' y0 y1 y0' y1' : ℝ)
    (hx0 : 0 ≤ x0') (hx1 : 0 ≤ x1') (hy0 : 0 ≤ y0) (hy1 : 0 ≤ y1)
    (h0 : x0' ≤ x0) (h1 : x1' ≤ x1) (g0 : y0 ≤ y0') (g1 : y1 ≤ y1') :
    ∃ α β : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ β ∧ β ≤ 1 ∧
      (x0 + x1) * α + (x0' + x1') * β = x0 + x1' ∧
      (y0 + y1) * α + (y0' + y1') * β = y0 + y1' := by
  obtain ⟨d0, hd0, rfl⟩ : ∃ d, 0 ≤ d ∧ x0 = x0' + d := ⟨x0 - x0', by linarith, by ring⟩
  obtain ⟨d1, hd1, rfl⟩ : ∃ d, 0 ≤ d ∧ x1 = x1' + d := ⟨x1 - x1', by linarith, by ring⟩
  obtain ⟨e0, he0, rfl⟩ : ∃ d, 0 ≤ d ∧ y0' = y0 + d := ⟨y0' - y0, by linarith, by ring⟩
  obtain ⟨e1, he1, rfl⟩ : ∃ d, 0 ≤ d ∧ y1' = y1 + d := ⟨y1' - y1, by linarith, by ring⟩
  by_cases hD : d0 + d1 = 0
  · have e0' : d0 = 0 := by linarith
    have e1' : d1 = 0 := by linarith
    subst e0' e1'
    refine ⟨1 - e1 / (e0 + e1), e1 / (e0 + e1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : e1 / (e0 + e1) ≤ 1 := by
        rcases eq_or_lt_of_le (add_nonneg he0 he1) with h | h
        · rw [← h]; simp
        · rw [div_le_one h]; linarith
      linarith
    · have : 0 ≤ e1 / (e0 + e1) := div_nonneg he1 (add_nonneg he0 he1)
      linarith
    · exact div_nonneg he1 (add_nonneg he0 he1)
    · rcases eq_or_lt_of_le (add_nonneg he0 he1) with h | h
      · rw [← h]; simp
      · rw [div_le_one h]; linarith
    · ring
    · rcases eq_or_lt_of_le (add_nonneg he0 he1) with h | h
      · have : e1 = 0 := by linarith
        have : e0 = 0 := by linarith
        subst_vars; simp
      · field_simp
        ring
  · by_cases hE : e0 + e1 = 0
    · have e0' : e0 = 0 := by linarith
      have e1' : e1 = 0 := by linarith
      subst e0' e1'
      have hDp : 0 < d0 + d1 := lt_of_le_of_ne (add_nonneg hd0 hd1) (Ne.symm hD)
      refine ⟨d0 / (d0 + d1), 1 - d0 / (d0 + d1), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact div_nonneg hd0 hDp.le
      · rw [div_le_one hDp]; linarith
      · have : d0 / (d0 + d1) ≤ 1 := by rw [div_le_one hDp]; linarith
        linarith
      · have : 0 ≤ d0 / (d0 + d1) := div_nonneg hd0 hDp.le
        linarith
      · field_simp
        ring
      · ring
    · have hDp : 0 < d0 + d1 := lt_of_le_of_ne (add_nonneg hd0 hd1) (Ne.symm hD)
      have hEp : 0 < e0 + e1 := lt_of_le_of_ne (add_nonneg he0 he1) (Ne.symm hE)
      set det := (x0' + d0 + (x1' + d1)) * (y0 + e0 + (y1 + e1)) - (x0' + x1') * (y0 + y1) with hdet
      have hdp : 0 < det := by
        rw [hdet]
        nlinarith [mul_pos hDp hEp, mul_nonneg hx0 he0, mul_nonneg hx1 he1, mul_nonneg hx0 he1,
          mul_nonneg hx1 he0, mul_nonneg hd0 hy0, mul_nonneg hd0 hy1, mul_nonneg hd1 hy0,
          mul_nonneg hd1 hy1]
      have hT0 : 0 ≤ x0' + x1' := by linarith
      have hS1 : 0 ≤ y0 + y1 := by linarith
      have hn0 : 0 ≤ x0' + d0 + x1' := by linarith
      have hn1 : 0 ≤ y0 + y1 + e1 := by linarith
      have hT1 : 0 ≤ y0 + e0 + (y1 + e1) := by linarith
      have hS0 : 0 ≤ x0' + d0 + (x1' + d1) := by linarith
      refine ⟨((x0' + d0 + x1') * (y0 + e0 + (y1 + e1)) - (y0 + y1 + e1) * (x0' + x1')) / det,
        ((x0' + d0 + (x1' + d1)) * (y0 + y1 + e1) - (y0 + y1) * (x0' + d0 + x1')) / det,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply div_nonneg _ hdp.le
        nlinarith [mul_nonneg hT0 he0, mul_nonneg hd0 hn1, mul_nonneg hd0 he0]
      · rw [div_le_one hdp]
        nlinarith [mul_nonneg hT1 hd1, mul_nonneg hT0 he1]
      · apply div_nonneg _ hdp.le
        nlinarith [mul_nonneg hn0 he1, mul_nonneg hd1 hS1, mul_nonneg hd1 he1]
      · rw [div_le_one hdp]
        nlinarith [mul_nonneg hS0 he0, mul_nonneg hS1 hd0]
      · field_simp
        ring
      · field_simp
        ring


/-- Real-valued dominance on mass functions. -/
def Dom' {S T : Type} [Fintype S] [Fintype T] (p : Bool → S → ℝ) (q : Bool → T → ℝ) : Prop :=
  ∃ K : S → T → ℝ, (∀ s t, 0 ≤ K s t) ∧ (∀ s, ∑ t, K s t = 1) ∧
    ∀ h t, q h t = ∑ s, p h s * K s t

lemma Dom'.trans {S T R : Type} [Fintype S] [Fintype T] [Fintype R]
    {p : Bool → S → ℝ} {q : Bool → T → ℝ} {r : Bool → R → ℝ}
    (h1 : Dom' p q) (h2 : Dom' q r) : Dom' p r := by
  obtain ⟨K, hK0, hK1, hK⟩ := h1
  obtain ⟨L, hL0, hL1, hL⟩ := h2
  refine ⟨fun s r => ∑ t, K s t * L t r, fun s r => Finset.sum_nonneg fun t _ =>
    mul_nonneg (hK0 _ _) (hL0 _ _), fun s => ?_, fun h r => ?_⟩
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hL1, mul_one, hK1]
  · rw [hL]
    simp_rw [hK, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp_rw [Finset.mul_sum, mul_assoc]

lemma Dom'.refl {S : Type} [Fintype S] [DecidableEq S] (p : Bool → S → ℝ) : Dom' p p :=
  ⟨fun s t => if s = t then 1 else 0, fun s t => by dsimp only; split_ifs <;> norm_num,
    fun s => by simp, fun h t => by simp⟩

lemma Dom'.equiv {S T S' T' : Type} [Fintype S] [Fintype T] [Fintype S'] [Fintype T']
    {p : Bool → S → ℝ} {q : Bool → T → ℝ} (e : S' ≃ S) (e' : T' ≃ T) (hd : Dom' p q) :
    Dom' (fun h s => p h (e s)) (fun h t => q h (e' t)) := by
  obtain ⟨K, hK0, hK1, hK⟩ := hd
  refine ⟨fun s t => K (e s) (e' t), fun _ _ => hK0 _ _, fun s => ?_, fun h t => ?_⟩
  · rw [← hK1 (e s)]
    exact e'.sum_comp (fun t => K (e s) t)
  · show q h (e' t) = _
    rw [hK]
    exact (e.sum_comp (fun s => p h s * K s (e' t))).symm

lemma bit_cases (b : Bit) : b = 0 ∨ b = 1 := by
  fin_cases b
  exacts [Or.inl rfl, Or.inr rfl]

lemma sum_bit (f : Bit → ℝ) : ∑ b, f b = f 0 + f 1 := by
  rw [show (Finset.univ : Finset Bit) = {0, 1} from by decide]
  simp

/-- Mass of the cell `U_c = i, V_c = j, W = w`. -/
def pm {Ω Wt : Type} [Fintype Ω] [DecidableEq Wt] (a : Bool → Ω → ℝ) (I J : Ω → Bit)
    (W : Ω → Wt) (h : Bool) (i j : Bit) (w : Wt) : ℝ :=
  ∑ ω, a h ω * (if I ω = i ∧ J ω = j ∧ W ω = w then 1 else 0)

lemma pm_nonneg {Ω Wt : Type} [Fintype Ω] [DecidableEq Wt] (a : Bool → Ω → ℝ)
    (ha : ∀ h ω, 0 ≤ a h ω) (I J : Ω → Bit) (W : Ω → Wt) (h : Bool) (i j : Bit) (w : Wt) :
    0 ≤ pm a I J W h i j w :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (ha _ _) (by split_ifs <;> norm_num)

lemma L1 {Ω Wt : Type} [Fintype Ω] [DecidableEq Wt] (a : Bool → Ω → ℝ) (I J : Ω → Bit)
    (W : Ω → Wt) (h : Bool) (i : Bit) (w : Wt) :
    ∑ ω, a h ω * (if (I ω, W ω) = (i, w) then 1 else 0) =
      pm a I J W h i 0 w + pm a I J W h i 1 w := by
  unfold pm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← mul_add]
  congr 1
  rcases bit_cases (J ω) with hj | hj <;> simp [hj, Prod.ext_iff]

lemma L2 {Ω Wt : Type} [Fintype Ω] [DecidableEq Wt] (a : Bool → Ω → ℝ) (I J : Ω → Bit)
    (W : Ω → Wt) (h : Bool) (s : Bit) (w : Wt) :
    ∑ ω, a h ω * (if (I ω + J ω, W ω) = (s, w) then 1 else 0) =
      pm a I J W h 0 s w + pm a I J W h 1 (s + 1) w := by
  unfold pm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← mul_add]
  congr 1
  have h11 : (1 : Bit) + 1 = 0 := by decide
  rcases bit_cases (I ω) with hi | hi <;> rcases bit_cases s with hs | hs <;>
    rcases bit_cases (J ω) with hj | hj <;>
    simp [hi, hs, hj, h11, Prod.ext_iff]


def Mfun (α β : ℝ) (i s : Bit) : ℝ :=
  if i = 0 then (if s = 0 then α else 1 - α) else (if s = 0 then β else 1 - β)

lemma step {Ω Wt : Type} [Fintype Ω] [Fintype Wt] [DecidableEq Wt]
    (a : Bool → Ω → ℝ) (ha : ∀ h ω, 0 ≤ a h ω) (I J : Ω → Bit) (W : Ω → Wt)
    (m0 : ∀ j w, pm a I J W false 1 j w ≤ pm a I J W false 0 j w)
    (m1 : ∀ j w, pm a I J W true 0 j w ≤ pm a I J W true 1 j w) :
    Dom' (fun h (t : Bit × Wt) => ∑ ω, a h ω * (if (I ω, W ω) = t then 1 else 0))
      (fun h (t : Bit × Wt) => ∑ ω, a h ω * (if (I ω + J ω, W ω) = t then 1 else 0)) := by
  have hex : ∀ w : Wt, ∃ α β : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ β ∧ β ≤ 1 ∧
      (pm a I J W false 0 0 w + pm a I J W false 0 1 w) * α +
        (pm a I J W false 1 0 w + pm a I J W false 1 1 w) * β =
        pm a I J W false 0 0 w + pm a I J W false 1 1 w ∧
      (pm a I J W true 0 0 w + pm a I J W true 0 1 w) * α +
        (pm a I J W true 1 0 w + pm a I J W true 1 1 w) * β =
        pm a I J W true 0 0 w + pm a I J W true 1 1 w := by
    intro w
    have := twoByTwo (pm a I J W false 0 0 w) (pm a I J W false 0 1 w)
      (pm a I J W false 1 0 w) (pm a I J W false 1 1 w)
      (pm a I J W true 0 0 w) (pm a I J W true 0 1 w)
      (pm a I J W true 1 0 w) (pm a I J W true 1 1 w)
      (pm_nonneg a ha I J W _ _ _ _) (pm_nonneg a ha I J W _ _ _ _)
      (pm_nonneg a ha I J W _ _ _ _) (pm_nonneg a ha I J W _ _ _ _)
      (m0 0 w) (m0 1 w) (m1 0 w) (m1 1 w)
    exact this
  choose α β hα0 hα1 hβ0 hβ1 hq0 hq1 using hex
  refine ⟨fun it st => if st.2 = it.2 then Mfun (α it.2) (β it.2) it.1 st.1 else 0,
    fun it st => ?_, fun it => ?_, fun h st => ?_⟩
  · obtain ⟨i, w⟩ := it
    obtain ⟨s, w'⟩ := st
    dsimp only
    split_ifs
    · have := hα0 w; have := hα1 w; have := hβ0 w; have := hβ1 w
      unfold Mfun; split_ifs <;> linarith
    · exact le_refl _
  · obtain ⟨i, w⟩ := it
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sum_bit]
    have := hα0 w; have := hα1 w; have := hβ0 w; have := hβ1 w
    unfold Mfun
    rcases bit_cases i with hi | hi <;> simp [hi]
  · obtain ⟨s, w'⟩ := st
    rw [Fintype.sum_prod_type]
    simp only [L2 a I J W]
    simp only [L1 a I J W]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [sum_bit]
    have e1 := hq0 w'
    have e2 := hq1 w'
    have h11 : (1 : Bit) + 1 = 0 := by decide
    unfold Mfun
    rcases bit_cases s with hs | hs <;> cases h <;> simp [hs, h11] <;> linarith


lemma pm_mono {k : ℕ} (c : Fin k) (R : Vec k × Vec k → Prop) [DecidablePred R]
    (hR : ∀ u v x, R (Function.update u c x, v) ↔ R (u, v)) (a : Vec k × Vec k → ℝ)
    (j x y : Bit)
    (hm : ∀ u v, a (Function.update u c x, v) ≤ a (Function.update u c y, v)) :
    ∑ ω, a ω * (if ω.1 c = x ∧ ω.2 c = j ∧ R ω then 1 else 0) ≤
      ∑ ω, a ω * (if ω.1 c = y ∧ ω.2 c = j ∧ R ω then 1 else 0) := by
  classical
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  calc ∑ ω ∈ Finset.univ.filter (fun ω : Vec k × Vec k => ω.1 c = x ∧ ω.2 c = j ∧ R ω), a ω
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Vec k × Vec k => ω.1 c = x ∧ ω.2 c = j ∧ R ω),
          a (Function.update ω.1 c y, ω.2) := by
        refine Finset.sum_le_sum fun ω hω => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
        have : ω = (Function.update ω.1 c x, ω.2) := by
          ext1
          · simp [hω.1]
          · rfl
        calc a ω = a (Function.update ω.1 c x, ω.2) := by rw [← this]
          _ ≤ _ := hm _ _
    _ = ∑ ω ∈ Finset.univ.filter (fun ω : Vec k × Vec k => ω.1 c = y ∧ ω.2 c = j ∧ R ω), a ω := by
        refine Finset.sum_nbij' (fun ω => (Function.update ω.1 c y, ω.2))
          (fun ω => (Function.update ω.1 c x, ω.2)) ?_ ?_ ?_ ?_ ?_
        · intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
          refine ⟨by simp, hω.2.1, ?_⟩
          rw [hR]; exact hω.2.2
        · intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
          refine ⟨by simp, hω.2.1, ?_⟩
          rw [hR]; exact hω.2.2
        · intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
          ext1
          · simp [hω.1]
          · rfl
        · intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
          ext1
          · simp [hω.1]
          · rfl
        · intro ω hω
          rfl


def fl {k : ℕ} (ℓ : ℕ) (uv : Vec k × Vec k) : Vec k :=
  fun i => if i.val < ℓ then uv.1 i + uv.2 i else uv.1 i

def Mf {k : ℕ} (P : Experiment (Vec k × Vec k)) (ℓ : ℕ) (h : Bool) (t : Vec k) : ℝ :=
  ∑ ω, (P h ω).toReal * (if fl ℓ ω = t then 1 else 0)

lemma stepℓ {k : ℕ} (P : Experiment (Vec k × Vec k))
    (h₀ : ∀ (v u : Vec k) (i : Fin k),
      (P false (Function.update u i 1, v)).toReal ≤
        (P false (Function.update u i 0, v)).toReal)
    (h₁ : ∀ (v u : Vec k) (i : Fin k),
      (P true (Function.update u i 0, v)).toReal ≤
        (P true (Function.update u i 1, v)).toReal)
    (ℓ : ℕ) (hℓ : ℓ < k) : Dom' (Mf P ℓ) (Mf P (ℓ + 1)) := by
  classical
  set c : Fin k := ⟨ℓ, hℓ⟩ with hc
  let Wt := {x : Vec k // x c = 0}
  let I : Vec k × Vec k → Bit := fun ω => ω.1 c
  let J : Vec k × Vec k → Bit := fun ω => ω.2 c
  let W : Vec k × Vec k → Wt := fun ω => ⟨Function.update (fl ℓ ω) c 0, by simp⟩
  let a : Bool → Vec k × Vec k → ℝ := fun h ω => (P h ω).toReal
  let φ : Bit × Wt ≃ Vec k :=
    { toFun := fun it => Function.update it.2.1 c it.1
      invFun := fun t => (t c, ⟨Function.update t c 0, by simp⟩)
      left_inv := fun it => by
        obtain ⟨i, x, hx⟩ := it
        ext1
        · simp
        · apply Subtype.ext
          simp only
          rw [Function.update_idem]
          rw [← hx]; simp
      right_inv := fun t => by simp }
  have hf1 : ∀ ω, fl ℓ ω = φ (I ω, W ω) := by
    intro ω
    funext i
    by_cases hi : i = c
    · subst hi
      simp [φ, I, W, fl, hc]
    · simp [φ, I, W, Function.update_of_ne hi]
  have hf2 : ∀ ω, fl (ℓ + 1) ω = φ (I ω + J ω, W ω) := by
    intro ω
    funext i
    by_cases hi : i = c
    · subst hi
      simp [φ, I, J, W, fl, hc]
    · have hne : i.val ≠ ℓ := fun h => hi (Fin.ext h)
      have : i.val < ℓ + 1 ↔ i.val < ℓ := by omega
      simp [φ, I, J, W, Function.update_of_ne hi, fl, this]
  have hW : ∀ u v x, W (Function.update u c x, v) = W (u, v) := by
    intro u v x
    apply Subtype.ext
    funext i
    by_cases hi : i = c
    · subst hi; simp [W]
    · simp [W, Function.update_of_ne hi, fl, hi]
  have hm0 : ∀ j w, pm a I J W false 1 j w ≤ pm a I J W false 0 j w := by
    intro j w
    unfold pm
    have := pm_mono c (fun ω => W ω = w) (fun u v x => by simp only [hW]) (a false) j 1 0
      (fun u v => h₀ v u c)
    simpa [I, J] using this
  have hm1 : ∀ j w, pm a I J W true 0 j w ≤ pm a I J W true 1 j w := by
    intro j w
    unfold pm
    have := pm_mono c (fun ω => W ω = w) (fun u v x => by simp only [hW]) (a true) j 0 1
      (fun u v => h₁ v u c)
    simpa [I, J] using this
  have hd := step a (fun h ω => ENNReal.toReal_nonneg) I J W hm0 hm1
  have := Dom'.equiv φ.symm φ.symm hd
  have e1 : Mf P ℓ = fun h t => ∑ ω, a h ω *
      (if (I ω, W ω) = φ.symm t then 1 else 0) := by
    funext h t
    unfold Mf
    refine Finset.sum_congr rfl fun ω _ => ?_
    congr 2
    rw [hf1, Equiv.apply_eq_iff_eq_symm_apply]
  have e2 : Mf P (ℓ + 1) = fun h t => ∑ ω, a h ω *
      (if (I ω + J ω, W ω) = φ.symm t then 1 else 0) := by
    funext h t
    unfold Mf
    refine Finset.sum_congr rfl fun ω _ => ?_
    congr 2
    rw [hf2, Equiv.apply_eq_iff_eq_symm_apply]
  rw [e1, e2]
  exact this

lemma map_toReal {S T : Type} [Fintype S] [Fintype T] [DecidableEq T]
    (μ : PMF S) (f : S → T) (t : T) :
    ((μ.map f) t).toReal = ∑ s, (μ s).toReal * (if f s = t then 1 else 0) := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : f s = t
    · simp [h]
    · simp [h, Ne.symm h]
  · intro s _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · simp

lemma chain {k : ℕ} (P : Experiment (Vec k × Vec k))
    (h₀ : ∀ (v u : Vec k) (i : Fin k),
      (P false (Function.update u i 1, v)).toReal ≤
        (P false (Function.update u i 0, v)).toReal)
    (h₁ : ∀ (v u : Vec k) (i : Fin k),
      (P true (Function.update u i 0, v)).toReal ≤
        (P true (Function.update u i 1, v)).toReal) :
    ∀ ℓ, ℓ ≤ k → Dom' (Mf P 0) (Mf P ℓ) := by
  classical
  intro ℓ
  induction ℓ with
  | zero => intro _; exact Dom'.refl _
  | succ m ih =>
    intro hm
    exact (ih (by omega)).trans (stepℓ P h₀ h₁ m (by omega))

end BinarySketchTruncation.Dev.Prop3

namespace BinarySketchTruncation.Opposite.Supplement
open BinarySketchTruncation.Dev.Prop3

theorem chk_proposition_3 {k : ℕ} (P : Experiment (Vec k × Vec k))
    (h₀ : ∀ (v u : Vec k) (i : Fin k),
      (P false (Function.update u i 1, v)).toReal ≤
        (P false (Function.update u i 0, v)).toReal)
    (h₁ : ∀ (v u : Vec k) (i : Fin k),
      (P true (Function.update u i 0, v)).toReal ≤
        (P true (Function.update u i 1, v)).toReal) :
    Dominates (fun h => (P h).map Prod.fst)
      (fun h => (P h).map (fun uv => uv.1 + uv.2)) := by
  classical
  obtain ⟨K, hK0, hK1, hK⟩ := chain P h₀ h₁ k le_rfl
  refine ⟨K, ⟨hK0, hK1⟩, fun h t => ?_⟩
  have e0 : ∀ ω : Vec k × Vec k, fl 0 ω = ω.1 := fun ω => by
    funext i; simp [fl]
  have ek : ∀ ω : Vec k × Vec k, fl k ω = ω.1 + ω.2 := fun ω => by
    funext i; simp [fl, i.isLt]
  have eA : ∀ s, (((P h).map Prod.fst) s).toReal = Mf P 0 h s := by
    intro s; rw [map_toReal]; unfold Mf; simp only [e0]
  have eB : (((P h).map (fun uv => uv.1 + uv.2)) t).toReal = Mf P k h t := by
    rw [map_toReal]; unfold Mf; simp only [ek]
  show (((P h).map (fun uv => uv.1 + uv.2)) t).toReal = ∑ s, (((P h).map Prod.fst) s).toReal * K s t
  rw [eB, hK]
  simp only [eA]

end BinarySketchTruncation.Opposite.Supplement
end

theorem solution : type_of% @BinarySketchTruncation.Opposite.Supplement.chk_proposition_3 := @BinarySketchTruncation.Opposite.Supplement.chk_proposition_3
