-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctions.Quasi.quasi_l_proximity_theorem
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T06:59:37.855293+00:00
-- url     : https://prove2.me/submissions/7649719a-f6ce-427b-9ba3-cbca07cf56e6

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_SSQSB
import Definitions.Def_DiscreteConvex_LConvexFunctions_IndicatorVec
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBF
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctions_ArgMin

set_option autoImplicit false

section
namespace QuasiLProximityGap

private theorem gap_or_bound (s : Finset ℤ) (α : ℤ) (hα : 0 < α)
    (hs0 : 0 ∈ s) (hspos : ∀ z ∈ s, 0 ≤ z) :
    (∀ z ∈ s, z ≤ ((s.card : ℤ)-1)*(α-1)) ∨
    ∃ b ∈ s, 0 ≤ b ∧ (∃ c ∈ s, b+α ≤ c) ∧
      ∀ z ∈ s, z ≤ b ∨ b+α ≤ z := by
  classical
  revert hs0 hspos
  refine Finset.strongInductionOn s ?_
  intro s ih hs0 hspos
  let m := s.max' ⟨0,hs0⟩
  have hm : m ∈ s := Finset.max'_mem s ⟨0,hs0⟩
  have hmax (z : ℤ) (hz : z ∈ s) : z ≤ m := Finset.le_max' s z hz
  have hmpos : 0 ≤ m := hspos m hm
  have hapos : 0 ≤ α-1 := by omega
  have hcardpos : 0 ≤ (s.card : ℤ)-1 := by
    have h := Finset.card_pos.mpr ⟨0,hs0⟩
    omega
  by_cases hm0 : m = 0
  · left
    intro z hz
    have hz0 : z ≤ 0 := by simpa only [hm0] using hmax z hz
    exact hz0.trans (mul_nonneg hcardpos hapos)
  let t := s.erase m
  have ht0 : 0 ∈ t := Finset.mem_erase.mpr ⟨Ne.symm hm0,hs0⟩
  have htpos : ∀ z ∈ t, 0 ≤ z := fun z hz => hspos z (Finset.mem_of_mem_erase hz)
  have htss : t ⊂ s := Finset.erase_ssubset hm
  rcases ih t htss ht0 htpos with htbound | ⟨b,hbt,hb0,⟨c,hct,hbc⟩,hgap⟩
  · let b := t.max' ⟨0,ht0⟩
    have hbt : b ∈ t := Finset.max'_mem t ⟨0,ht0⟩
    have hbs : b ∈ s := Finset.mem_of_mem_erase hbt
    have hbmax (z : ℤ) (hz : z ∈ t) : z ≤ b := Finset.le_max' t z hz
    by_cases hmb : m ≤ b+(α-1)
    · left
      intro z hz
      have hbtbound := htbound b hbt
      have hcard : (t.card : ℤ)+1 = (s.card : ℤ) := by
        exact_mod_cast Finset.card_erase_add_one hm
      have hzmax := hmax z hz
      nlinarith
    · right
      have hbm : b+α ≤ m := by omega
      refine ⟨b,hbs,hspos b hbs,⟨m,hm,hbm⟩,?_⟩
      intro z hz
      by_cases hzm : z = m
      · exact Or.inr (hzm ▸ hbm)
      · exact Or.inl (hbmax z (Finset.mem_erase.mpr ⟨hzm,hz⟩))
  · right
    refine ⟨b,Finset.mem_of_mem_erase hbt,hb0,⟨c,Finset.mem_of_mem_erase hct,hbc⟩,?_⟩
    intro z hz
    by_cases hzm : z = m
    · right
      rw [hzm]
      exact hbc.trans (hmax c (Finset.mem_of_mem_erase hct))
    · exact hgap z (Finset.mem_erase.mpr ⟨hzm,hz⟩)

theorem exists_gap {V : Type*} [Fintype V] [DecidableEq V]
    (q : V → ℤ) (α : ℤ) (hα : 0 < α) (hnonneg : ∀ v, 0 ≤ q v)
    (hzero : ∃ v, q v = 0)
    (hlarge : ∃ v, ((Fintype.card V : ℤ)-1)*(α-1) < q v) :
    ∃ b : ℤ, 0 ≤ b ∧ (∃ v, b+α ≤ q v) ∧
      ∀ v, q v ≤ b ∨ b+α ≤ q v := by
  classical
  let s := Finset.univ.image q
  have hs0 : 0 ∈ s := by
    obtain ⟨v,hv⟩ := hzero
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ v,hv⟩
  have hspos : ∀ z ∈ s, 0 ≤ z := by
    intro z hz
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz
    exact hnonneg v
  have hqmem (v : V) : q v ∈ s := Finset.mem_image.mpr ⟨v,Finset.mem_univ v,rfl⟩
  rcases gap_or_bound s α hα hs0 hspos with hbound | ⟨b,_,hb0,⟨c,hc,hbc⟩,hgap⟩
  · obtain ⟨v,hv⟩ := hlarge
    have hb := hbound (q v) (hqmem v)
    have hc : (s.card : ℤ) ≤ Fintype.card V := by
      exact_mod_cast (Finset.card_image_le (s := Finset.univ) (f := q))
    have hd : 0 ≤ α-1 := by omega
    have hmul := mul_le_mul_of_nonneg_right (sub_le_sub_right hc 1) hd
    omega
  · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hc
    exact ⟨b,hb0,⟨v,hbc⟩,fun w => hgap (q w) (hqmem w)⟩

#print axioms exists_gap
end QuasiLProximityGap
end

section
open DiscreteConvex.LConvexFunctions DiscreteConvex.LConvexFunctions.Quasi
namespace QuasiLProximityCut
variable {V : Type*} [Fintype V] [DecidableEq V]

def cut (q : V → ℤ) (α : ℤ) (Y : Finset V) : V → ℤ :=
  fun v => q v - α * IndicatorVec Y v

lemma cut_le_of_zero_gap (g : (V → ℤ) → WithTop ℝ) (hs : SSQSB g)
    (hshift : ∀ (q : V → ℤ) (k : ℤ), g (fun v => q v + k) = g q)
    (h0 : g 0 ≠ ⊤) (α : ℤ) (hα : 0 ≤ α)
    (hloc : ∀ Y : Finset V, g 0 ≤ g (fun v => α * IndicatorVec Y v))
    (q : V → ℤ) (hq : g q ≠ ⊤) (Y : Finset V)
    (hhigh : ∀ v ∈ Y, α ≤ q v) (hlow : ∀ v ∉ Y, q v ≤ 0) :
    g (cut q α Y) ≤ g q := by
  let A : V → ℤ := fun v => max (q v) 0
  let C : V → ℤ := cut A α Y
  let D : V → ℤ := fun v => α * IndicatorVec Y v
  have hsup : (fun v => A v - α) ⊔ 0 = C := by
    funext v
    by_cases hv : v ∈ Y
    · have hh := hhigh v hv
      simp [C,cut,A,IndicatorVec,hv] <;> omega
    · have hl := hlow v hv
      simp [C,cut,A,IndicatorVec,hv] <;> omega
  have hinf : (fun v => A v - α) ⊓ 0 = fun v => D v - α := by
    funext v
    by_cases hv : v ∈ Y
    · have hh := hhigh v hv
      simp [D,A,IndicatorVec,hv] <;> omega
    · have hl := hlow v hv
      simp [D,A,IndicatorVec,hv] <;> omega
  have he1 : g C ≤ g A := by
    have he := (hs 0 (fun v => A v - α)).2
    rw [sup_comm,inf_comm] at he
    rw [hsup,hinf] at he
    have hh : g (fun v => D v-α) ≥ g 0 := by
      simpa only [sub_eq_add_neg,hshift,D] using hloc Y
    simpa only [sub_eq_add_neg,hshift] using he hh
  have hsup2 : q ⊔ C = A := by
    funext v
    by_cases hv : v ∈ Y
    · have hh := hhigh v hv
      simp [C,cut,A,IndicatorVec,hv] <;> omega
    · have hl := hlow v hv
      simp [C,cut,A,IndicatorVec,hv] <;> omega
  have hinf2 : q ⊓ C = cut q α Y := by
    funext v
    by_cases hv : v ∈ Y
    · have hh := hhigh v hv
      simp [C,cut,A,IndicatorVec,hv] <;> omega
    · have hl := hlow v hv
      simp [C,cut,A,IndicatorVec,hv] <;> omega
  have he2 := (hs q C).1
  rw [hsup2,hinf2] at he2
  exact he2 he1

theorem cut_le (g : (V → ℤ) → WithTop ℝ) (hs : SSQSB g)
    (hshift : ∀ (q : V → ℤ) (k : ℤ), g (fun v => q v + k) = g q)
    (h0 : g 0 ≠ ⊤) (α : ℤ) (hα : 0 ≤ α)
    (hloc : ∀ Y : Finset V, g 0 ≤ g (fun v => α * IndicatorVec Y v))
    (q : V → ℤ) (hq : g q ≠ ⊤) (Y : Finset V) (b : ℤ)
    (hhigh : ∀ v ∈ Y, b + α ≤ q v) (hlow : ∀ v ∉ Y, q v ≤ b) :
    g (cut q α Y) ≤ g q := by
  let r : V → ℤ := fun v => q v - b
  have hr : g r = g q := hshift q (-b)
  have hh : ∀ v ∈ Y, α ≤ r v := by intro v hv; have := hhigh v hv; dsimp [r]; omega
  have hl : ∀ v ∉ Y, r v ≤ 0 := by intro v hv; have := hlow v hv; dsimp [r]; omega
  have he := cut_le_of_zero_gap g hs hshift h0 α hα hloc r (hr ▸ hq) Y hh hl
  have hc : cut r α Y = fun v => cut q α Y v - b := by
    funext v
    dsimp [cut,r]
    omega
  rw [hc,hr] at he
  simpa only [sub_eq_add_neg,hshift] using he

end QuasiLProximityCut
#print axioms QuasiLProximityCut.cut_le
end

section
open DiscreteConvex.LConvexFunctions DiscreteConvex.LConvexFunctions.Quasi
namespace QuasiLProximityCompression
open QuasiLProximityCut
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every finite normalized point is dominated by a point in the sharp proximity box. -/
theorem compress (g : (V → ℤ) → WithTop ℝ) (hs : SSQSB g)
    (hshift : ∀ (q : V → ℤ) (k : ℤ), g (fun v => q v + k) = g q)
    (h0 : g 0 ≠ ⊤) (α : ℤ) (hα : 0 < α)
    (hloc : ∀ Y : Finset V, g 0 ≤ g (fun v => α * IndicatorVec Y v))
    (q : V → ℤ) (hq : g q ≠ ⊤) (hnonneg : ∀ v, 0 ≤ q v)
    (hzero : ∃ v, q v = 0) :
    ∃ r : V → ℤ, (∀ v, 0 ≤ r v ∧ r v ≤ ((Fintype.card V : ℤ)-1)*(α-1)) ∧
      g r ≤ g q := by
  classical
  suffices h : ∀ n : ℕ, ∀ q : V → ℤ, (∑ v, (q v).toNat) = n →
      g q ≠ ⊤ → (∀ v, 0 ≤ q v) → (∃ v, q v = 0) →
      ∃ r : V → ℤ, (∀ v, 0 ≤ r v ∧ r v ≤ ((Fintype.card V : ℤ)-1)*(α-1)) ∧
        g r ≤ g q by
    exact h _ q rfl hq hnonneg hzero
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q hn hq hnonneg hzero
    by_cases hbound : ∀ v, q v ≤ ((Fintype.card V : ℤ)-1)*(α-1)
    · exact ⟨q,fun v => ⟨hnonneg v,hbound v⟩,le_rfl⟩
    have hlarge : ∃ v, ((Fintype.card V : ℤ)-1)*(α-1) < q v := by
      simpa only [not_forall,not_le] using hbound
    obtain ⟨b,hb,⟨u,hu⟩,hgap⟩ := QuasiLProximityGap.exists_gap q α hα hnonneg hzero hlarge
    let Y : Finset V := Finset.univ.filter (fun v => b+α ≤ q v)
    let q' := cut q α Y
    have hY (v : V) : v ∈ Y ↔ b+α ≤ q v := by simp [Y]
    have hhigh : ∀ v ∈ Y, b+α ≤ q v := fun v hv => (hY v).mp hv
    have hlow : ∀ v ∉ Y, q v ≤ b := by
      intro v hv
      exact (hgap v).resolve_right (fun h => hv ((hY v).mpr h))
    have hnonneg' (v : V) : 0 ≤ q' v := by
      by_cases hv : v ∈ Y
      · have hh := hhigh v hv
        simp [q',cut,IndicatorVec,hv]
        omega
      · simpa [q',cut,IndicatorVec,hv] using hnonneg v
    have hzero' : ∃ v, q' v = 0 := by
      obtain ⟨v,hv⟩ := hzero
      have hvY : v ∉ Y := by rw [hY]; omega
      exact ⟨v,by simpa [q',cut,IndicatorVec,hvY] using hv⟩
    have hval : g q' ≤ g q := cut_le g hs hshift h0 α hα.le hloc q hq Y b hhigh hlow
    have hmeasure : (∑ v, (q' v).toNat) < n := by
      rw [← hn]
      apply Finset.sum_lt_sum
      · intro v _
        have hp := hnonneg v
        have hp' := hnonneg' v
        by_cases hv : v ∈ Y
        · have hh : q' v = q v - α := by simp [q',cut,IndicatorVec,hv]
          omega
        · have hh : q' v = q v := by simp [q',cut,IndicatorVec,hv]
          omega
      · refine ⟨u,Finset.mem_univ u,?_⟩
        have huY := (hY u).mpr hu
        have hp := hnonneg u
        have hp' := hnonneg' u
        have hh : q' u = q u - α := by simp [q',cut,IndicatorVec,huY]
        omega
    obtain ⟨r,hr,he⟩ := ih _ hmeasure q' rfl (ne_top_of_le_ne_top hq hval) hnonneg' hzero'
    exact ⟨r,hr,he.trans hval⟩

end QuasiLProximityCompression
#print axioms QuasiLProximityCompression.compress
end

section
namespace QuasiLProximityBox
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem shift_invariant_of_unit (g : (V → ℤ) → WithTop ℝ)
    (hunit : ∀ p : V → ℤ, g (fun v => p v+1) = g p) :
    ∀ p : V → ℤ, ∀ a : ℤ, g (fun v => p v+a) = g p := by
  have hperiod : Function.Periodic g (1 : V → ℤ) := hunit
  intro p a
  convert hperiod.zsmul a p using 1
  congr 1
  funext v
  simp

theorem exists_box_minimum (g : (V → ℤ) → WithTop ℝ) (α : ℤ) (hα : 0 < α)
    (hshift : ∀ p : V → ℤ, ∀ a : ℤ, g (fun v => p v+a) = g p)
    (hcompress : ∀ q : V → ℤ, g q ≠ ⊤ → (∀ v, 0 ≤ q v) → (∃ v, q v=0) →
      ∃ r : V → ℤ, (∀ v, 0 ≤ r v ∧ r v ≤ ((Fintype.card V : ℤ)-1)*(α-1)) ∧
        g r ≤ g q) :
    ∃ r : V → ℤ, (∀ q, g r ≤ g q) ∧
      ∀ v, 0 ≤ r v ∧ r v ≤ ((Fintype.card V : ℤ)-1)*(α-1) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI := h
    refine ⟨0,?_,?_⟩
    · intro q
      have he : q=0 := Subsingleton.elim _ _
      rw [he]
    · intro v
      exact isEmptyElim v
  | inr h =>
    letI := h
    let R : ℤ := ((Fintype.card V : ℤ)-1)*(α-1)
    have hR : 0 ≤ R := by
      have hn : 0 < Fintype.card V := Fintype.card_pos
      have h1 : 0 ≤ (Fintype.card V : ℤ)-1 := by omega
      have h2 : 0 ≤ α-1 := by omega
      exact mul_nonneg h1 h2
    let B := Fintype.piFinset (fun _ : V => Finset.Icc (0 : ℤ) R)
    have hB : B.Nonempty := by
      refine ⟨0, Fintype.mem_piFinset.mpr ?_⟩
      intro v
      exact Finset.mem_Icc.mpr ⟨le_rfl,hR⟩
    obtain ⟨r,hr,hmin⟩ := Finset.exists_min_image B g hB
    refine ⟨r,?_,?_⟩
    · intro q
      by_cases hq : g q = ⊤
      · simp [hq]
      obtain ⟨u,_,hu⟩ := Finset.exists_min_image Finset.univ q Finset.univ_nonempty
      let q' : V → ℤ := fun v => q v-q u
      have hq'pos (v : V) : 0 ≤ q' v := sub_nonneg.mpr (hu v (Finset.mem_univ v))
      have hq'zero : ∃ v, q' v=0 := ⟨u,sub_self _⟩
      have hcost : g q'=g q := by
        simpa only [q',sub_eq_add_neg] using hshift q (-q u)
      have hq'fin : g q' ≠ ⊤ := by rwa [hcost]
      obtain ⟨r',hr',hle⟩ := hcompress q' hq'fin hq'pos hq'zero
      have hr'B : r' ∈ B := Fintype.mem_piFinset.mpr (fun v => Finset.mem_Icc.mpr (hr' v))
      exact (hmin r' hr'B).trans (hcost ▸ hle)
    · intro v
      exact Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hr v)

#print axioms shift_invariant_of_unit
#print axioms exists_box_minimum
end QuasiLProximityBox
end

section
open DiscreteConvex.LConvexFunctions DiscreteConvex.LConvexFunctions.Quasi
namespace QuasiLProximityAssembly
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem directed_proximity (g : (V → ℤ) → WithTop ℝ) (hs : SSQSB g)
    (hunit : ∀ q : V → ℤ, g (fun v => q v+1) = g q)
    (p : V → ℤ) (hp : g p ≠ ⊤) (α : ℤ) (hα : 0 < α)
    (hloc : ∀ Y : Finset V, g p ≤ g (fun v => p v+α*IndicatorVec Y v)) :
    ∃ r : V → ℤ, (∀ q, g r ≤ g q) ∧
      ∀ v, p v ≤ r v ∧ r v ≤ p v+((Fintype.card V : ℤ)-1)*(α-1) := by
  let F : (V → ℤ) → WithTop ℝ := fun q => g (fun v => p v+q v)
  have hFs : SSQSB F := by
    intro q r
    have hh := hs (fun v => p v+q v) (fun v => p v+r v)
    have hsup : (fun v => p v+q v) ⊔ (fun v => p v+r v) =
        (fun v => p v+(q ⊔ r) v) := by
      funext v
      change max (p v+q v) (p v+r v) = p v+max (q v) (r v)
      omega
    have hinf : (fun v => p v+q v) ⊓ (fun v => p v+r v) =
        (fun v => p v+(q ⊓ r) v) := by
      funext v
      change min (p v+q v) (p v+r v) = p v+min (q v) (r v)
      omega
    simpa only [hsup,hinf] using hh
  have hshift := QuasiLProximityBox.shift_invariant_of_unit g hunit
  have hFshift (q : V → ℤ) (a : ℤ) : F (fun v => q v+a) = F q := by
    simpa only [F,add_assoc] using hshift (fun v => p v+q v) a
  have hF0 : F 0 ≠ ⊤ := by simpa [F] using hp
  have hFloc (Y : Finset V) : F 0 ≤ F (fun v => α*IndicatorVec Y v) := by
    simpa [F] using hloc Y
  obtain ⟨r,hrmin,hrbound⟩ := QuasiLProximityBox.exists_box_minimum F α hα hFshift
    (QuasiLProximityCompression.compress F hFs hFshift hF0 α hα hFloc)
  refine ⟨fun v => p v+r v,?_,?_⟩
  · intro q
    have hh := hrmin (fun v => q v-p v)
    have he : (fun v => p v+(q v-p v)) = q := by funext v; omega
    simpa only [F,he] using hh
  · intro v
    have hh := hrbound v
    dsimp only
    omega

end QuasiLProximityAssembly
#print axioms QuasiLProximityAssembly.directed_proximity
end

open DiscreteConvex.LConvexFunctions DiscreteConvex.LConvexFunctions.Quasi

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (α : ℤ) (hα : 0 < α)
    (g : (V → ℤ) → WithTop ℝ) (hper : ∀ p : V → ℤ, g (fun v => p v + 1) = g p)
    (hg : SSQSB g) (pα : V → ℤ) (hpα : pα ∈ DomZ g)
    (hloc : ∀ Y : Finset V, g pα ≤ g (fun v => pα v + α * IndicatorVec Y v)) :
    (ArgMin g).Nonempty ∧ ∃ p ∈ ArgMin g, ∀ v : V,
      pα v ≤ p v ∧ p v ≤ pα v + ((Fintype.card V : ℤ) - 1) * (α - 1) := by
  obtain ⟨r,hmin,hbound⟩ := QuasiLProximityAssembly.directed_proximity g hg hper pα hpα α hα hloc
  exact ⟨⟨r,hmin⟩,r,hmin,hbound⟩

#print axioms solution
