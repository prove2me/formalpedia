-- Prove2me | solution 1 for CrossLicensing.ExPost.equation_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T09:57:11.074984+00:00
-- url     : https://prove2.me/submissions/0d746f75-d948-4404-9388-6e96eed3993c

import Mathlib
import Definitions.Def_CrossLicensing_ExPost_Model
set_option autoImplicit false
namespace CrossResearch
open CrossLicensing.ExPost
lemma best_iff (A q : ℝ) (hq : 0 ≤ q) :
    (∀ x : ℝ, 0 ≤ x → (A-x)*x ≤ (A-q)*q) ↔
    (q=0 ∧ A≤0) ∨ (2*q=A ∧ 0≤A) := by
  constructor
  · intro h
    by_cases hA : A≤0
    · left
      have h0 := h 0 (by norm_num)
      have hp := mul_nonpos_of_nonpos_of_nonneg hA hq
      exact ⟨by nlinarith [sq_nonneg q],hA⟩
    · right
      have hA' : 0≤A/2 := by linarith
      have hv := h (A/2) hA'
      exact ⟨by nlinarith [sq_nonneg (q-A/2)],by linarith⟩
  · rintro (⟨rfl,hA⟩|⟨hA,hpos⟩) x hx
    · have := mul_nonpos_of_nonpos_of_nonneg (show A-x≤0 by linarith) hx
      simpa using this
    · nlinarith [sq_nonneg (x-q)]
def NE (A B : ℝ) (q : ℝ×ℝ) : Prop :=
  0≤q.1 ∧ 0≤q.2 ∧
  (∀ x : ℝ,0≤x→(A-x-q.2)*x≤(A-q.1-q.2)*q.1) ∧
  (∀ y : ℝ,0≤y→(B-y-q.1)*y≤(B-q.2-q.1)*q.2)
lemma ne_iff (A B : ℝ) (q : ℝ×ℝ) : NE A B q ↔
    0≤q.1 ∧ 0≤q.2 ∧
    ((q.1=0 ∧ A≤q.2) ∨ (2*q.1+q.2=A ∧ q.2≤A)) ∧
    ((q.2=0 ∧ B≤q.1) ∨ (2*q.2+q.1=B ∧ q.1≤B)) := by
  unfold NE
  constructor
  · rintro ⟨hq1,hq2,h1,h2⟩
    have h1' : ∀x:ℝ,0≤x→(A-q.2-x)*x≤(A-q.2-q.1)*q.1 := by
      intro x hx; convert h1 x hx using 1 <;> ring
    have h2' : ∀y:ℝ,0≤y→(B-q.1-y)*y≤(B-q.1-q.2)*q.2 := by
      intro y hy; convert h2 y hy using 1 <;> ring
    have h1b := (best_iff (A-q.2) q.1 hq1).mp h1'
    have h2b := (best_iff (B-q.1) q.2 hq2).mp h2'
    refine ⟨hq1,hq2,?_,?_⟩
    · rcases h1b with ⟨h,h'⟩|⟨h,h'⟩
      · exact Or.inl ⟨h,by linarith⟩
      · exact Or.inr ⟨by linarith,by linarith⟩
    · rcases h2b with ⟨h,h'⟩|⟨h,h'⟩
      · exact Or.inl ⟨h,by linarith⟩
      · exact Or.inr ⟨by linarith,by linarith⟩
  · rintro ⟨hq1,hq2,h1,h2⟩
    refine ⟨hq1,hq2,?_,?_⟩
    · have hb : (q.1=0 ∧ A-q.2≤0) ∨ (2*q.1=A-q.2 ∧ 0≤A-q.2) := by
        rcases h1 with ⟨h,h'⟩|⟨h,h'⟩
        · exact Or.inl ⟨h,by linarith⟩
        · exact Or.inr ⟨by linarith,by linarith⟩
      intro x hx
      convert (best_iff (A-q.2) q.1 hq1).mpr hb x hx using 1 <;> ring
    · have hb : (q.2=0 ∧ B-q.1≤0) ∨ (2*q.2=B-q.1 ∧ 0≤B-q.1) := by
        rcases h2 with ⟨h,h'⟩|⟨h,h'⟩
        · exact Or.inl ⟨h,by linarith⟩
        · exact Or.inr ⟨by linarith,by linarith⟩
      intro x hx
      convert (best_iff (B-q.1) q.2 hq2).mpr hb x hx using 1 <;> ring
lemma unique {A B : ℝ} {q r : ℝ×ℝ} (hq : NE A B q) (hr : NE A B r) : q=r := by
  obtain ⟨hq1,hq2,hqa,hqb⟩ := (ne_iff A B q).mp hq
  obtain ⟨hr1,hr2,hra,hrb⟩ := (ne_iff A B r).mp hr
  rcases hqa with ⟨hqa,hqa'⟩|⟨hqa,hqa'⟩ <;>
    rcases hqb with ⟨hqb,hqb'⟩|⟨hqb,hqb'⟩ <;>
    rcases hra with ⟨hra,hra'⟩|⟨hra,hra'⟩ <;>
    rcases hrb with ⟨hrb,hrb'⟩|⟨hrb,hrb'⟩ <;>
    ext <;> linarith
noncomputable def Q (A B : ℝ) : ℝ×ℝ :=
  if 0≤2*A-B then ((2*A-B)/3,(2*B-A)/3)
  else if 0≤B then (0,B/2) else (0,0)
lemma Q_ne {A B : ℝ} (hAB : A≤B) : NE A B (Q A B) := by
  apply (ne_iff A B _).mpr
  unfold Q
  split_ifs with h1 h2
  · dsimp
    refine ⟨by linarith,by linarith,Or.inr ⟨by ring,by linarith⟩,Or.inr ⟨by ring,by linarith⟩⟩
  · dsimp
    exact ⟨le_rfl,by linarith,Or.inl ⟨rfl,by linarith⟩,Or.inr ⟨by ring,h2⟩⟩
  · dsimp
    exact ⟨le_rfl,le_rfl,Or.inl ⟨rfl,by linarith⟩,Or.inl ⟨rfl,by linarith⟩⟩
lemma Q_total {A B : ℝ} (hAB : A≤B) :
    (Q A B).1+(Q A B).2=max 0 (max (B/2) ((A+B)/3)) := by
  unfold Q
  split_ifs with h1 h2
  · dsimp
    rw [max_eq_right (show B/2≤(A+B)/3 by linarith),max_eq_right (show 0≤(A+B)/3 by linarith)]
    ring
  · dsimp
    rw [max_eq_left (show (A+B)/3≤B/2 by linarith),max_eq_right (show 0≤B/2 by linarith)]
    ring
  · dsimp
    rw [max_eq_left (show (A+B)/3≤B/2 by linarith),max_eq_left (show B/2≤0 by linarith)]
    ring
lemma platform_ne (β T₁ T₂ r : ℝ) (q : ℝ×ℝ) :
    IsQuantityNE β T₁ T₂ r q ↔ NE (1+T₁+β*T₂-r) (1+T₂+β*T₁-r) q := by
  unfold IsQuantityNE IsNE payoff1 payoff2 NE
  simp only [Set.mem_Ici]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> refine ⟨h1,h2,?_,?_⟩
  · intro x hx; convert h3 x hx using 1 <;> ring
  · intro x hx; convert h4 x hx using 1 <;> ring
  · intro x hx; convert h3 x hx using 1 <;> ring
  · intro x hx; convert h4 x hx using 1 <;> ring
end CrossResearch
namespace CrossResearch
open CrossLicensing.ExPost
lemma intercept_order (β T₁ T₂ r : ℝ) (h : Standing β T₁ T₂ r) :
    1+T₁+β*T₂-r ≤ 1+T₂+β*T₁-r := by
  obtain ⟨hb0,hb1,hT1,hT12,hr⟩ := h
  nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hT12)]
lemma formula_eq (β T₁ T₂ r : ℝ) :
    quantityFormula β T₁ T₂ r = Q (1+T₁+β*T₂-r) (1+T₂+β*T₁-r) := by
  unfold quantityFormula Q r₁ r₂
  have h1 : (r≤1+T₁*(2-β)-T₂*(1-2*β)) ↔
      0≤2*(1+T₁+β*T₂-r)-(1+T₂+β*T₁-r) := by constructor <;> intro h <;> nlinarith
  have h2 : (r≤1+T₁*β+T₂) ↔ 0≤1+T₂+β*T₁-r := by constructor <;> intro h <;> nlinarith
  simp only [h1,h2]
  split_ifs <;> ext <;> dsimp <;> ring
lemma equation2 (β T₁ T₂ r : ℝ) (h : Standing β T₁ T₂ r) (q : ℝ×ℝ) :
    IsQuantityNE β T₁ T₂ r q ↔ q=quantityFormula β T₁ T₂ r := by
  rw [platform_ne,formula_eq]
  constructor
  · intro hq; exact unique hq (Q_ne (intercept_order β T₁ T₂ r h))
  · rintro rfl; exact Q_ne (intercept_order β T₁ T₂ r h)
lemma equation3 (β T₁ T₂ r : ℝ) (h : Standing β T₁ T₂ r) (q : ℝ×ℝ)
    (hq : IsQuantityNE β T₁ T₂ r q) :
    supplierProfit r q=supplierProfitFormula β T₁ T₂ r := by
  rw [(equation2 β T₁ T₂ r h q).mp hq]
  unfold supplierProfit quantityFormula supplierProfitFormula
  split_ifs <;> dsimp <;> ring
lemma root (β T₁ T₂ r : ℝ) (h : Standing β T₁ T₂ r) :
    (∃ q,IsQuantityNE β T₁ T₂ r q) ∧
    (∃ q,IsQuantityNE 0 T₁ T₂ r q) ∧
    (∀ qcl qn,IsQuantityNE β T₁ T₂ r qcl → IsQuantityNE 0 T₁ T₂ r qn →
      supplierProfit r qn ≤ supplierProfit r qcl) := by
  have hn : Standing 0 T₁ T₂ r := ⟨le_rfl,by norm_num,h.2.2⟩
  refine ⟨⟨quantityFormula β T₁ T₂ r,(equation2 β T₁ T₂ r h _).mpr rfl⟩,
    ⟨quantityFormula 0 T₁ T₂ r,(equation2 0 T₁ T₂ r hn _).mpr rfl⟩,?_⟩
  intro qcl qn hcl hqn
  rw [(equation2 β T₁ T₂ r h qcl).mp hcl,(equation2 0 T₁ T₂ r hn qn).mp hqn]
  unfold supplierProfit
  rw [formula_eq,formula_eq,Q_total (intercept_order 0 T₁ T₂ r hn),Q_total (intercept_order β T₁ T₂ r h)]
  apply mul_le_mul_of_nonneg_left _ h.2.2.2.2
  apply max_le_max le_rfl
  apply max_le_max
  · have := mul_nonneg h.1 h.2.2.1
    nlinarith
  · have hT2 : 0≤T₂ := le_trans h.2.2.1 h.2.2.2.1
    have h1 := mul_nonneg h.1 h.2.2.1
    have h2 := mul_nonneg h.1 hT2
    nlinarith
end CrossResearch

open CrossLicensing.ExPost

/-- Equation (2), read as an exact characterization of the quantity-game equilibrium. -/
theorem solution (β T₁ T₂ r : ℝ) (h : Standing β T₁ T₂ r) (q : ℝ × ℝ) :
    IsQuantityNE β T₁ T₂ r q ↔ q = quantityFormula β T₁ T₂ r := by exact CrossResearch.equation2 β T₁ T₂ r h q


#print axioms solution
