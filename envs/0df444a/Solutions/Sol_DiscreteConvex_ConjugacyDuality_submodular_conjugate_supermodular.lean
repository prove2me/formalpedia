-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDuality.submodular_conjugate_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:15:24.054082+00:00
-- url     : https://prove2.me/submissions/3b7ecd05-f70e-4201-9831-e3e023ca876c

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_SubmodularR
import Definitions.Def_DiscreteConvex_ConjugacyDuality_SupermodularEReal
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugateR

set_option autoImplicit false

namespace DiscreteConvex.ConjugacyDuality

lemma p2m_f79_rearr (a b c d : ℝ) :
    a * b + c * d ≤ (a ⊔ c) * (b ⊔ d) + (a ⊓ c) * (b ⊓ d) := by
  rcases le_total a c with h1 | h1 <;> rcases le_total b d with h2 | h2
  · rw [sup_of_le_right h1, sup_of_le_right h2, inf_of_le_left h1, inf_of_le_left h2]
    linarith
  · rw [sup_of_le_right h1, sup_of_le_left h2, inf_of_le_left h1, inf_of_le_right h2]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  · rw [sup_of_le_left h1, sup_of_le_right h2, inf_of_le_right h1, inf_of_le_left h2]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  · rw [sup_of_le_left h1, sup_of_le_left h2, inf_of_le_right h1, inf_of_le_right h2]

lemma p2m_f79_pair {V : Type*} [Fintype V] (y z x x' : V → ℝ) :
    (∑ i, y i * x i) + (∑ i, z i * x' i) ≤
      (∑ i, (y ⊔ z) i * (x ⊔ x') i) + (∑ i, (y ⊓ z) i * (x ⊓ x') i) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.sup_apply, Pi.inf_apply]
  exact p2m_f79_rearr _ _ _ _

lemma p2m_f79_mem {V : Type*} [Fintype V] (f : (V → ℝ) → WithTop ℝ) (p x : V → ℝ) :
    ((∑ i, p i * x i : ℝ) : EReal) - ToEReal (f x) ≤ ConvexConjugateR f p :=
  le_sSup ⟨x, rfl⟩

lemma p2m_f79_toE (r : ℝ) : ToEReal (r : WithTop ℝ) = (r : EReal) := rfl

lemma p2m_f79_toE_top : ToEReal (⊤ : WithTop ℝ) = (⊤ : EReal) := rfl

lemma p2m_f79_key {V : Type*} [Fintype V] (f : (V → ℝ) → WithTop ℝ)
    (hf : SubmodularR f) (y z x x' : V → ℝ) :
    ((∑ i, y i * x i : ℝ) : EReal) - ToEReal (f x) +
        (((∑ i, z i * x' i : ℝ) : EReal) - ToEReal (f x')) ≤
      ConvexConjugateR f (y ⊔ z) + ConvexConjugateR f (y ⊓ z) := by
  by_cases hx : f x = ⊤
  · rw [hx, p2m_f79_toE_top, EReal.sub_top, EReal.bot_add]
    exact bot_le
  by_cases hx' : f x' = ⊤
  · rw [hx', p2m_f79_toE_top, EReal.sub_top, EReal.add_bot]
    exact bot_le
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hx
  obtain ⟨r', hr'⟩ := WithTop.ne_top_iff_exists.1 hx'
  have hs := hf x x'
  rw [← hr, ← hr', ← WithTop.coe_add] at hs
  have hlt : f (x ⊔ x') + f (x ⊓ x') ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hs
  have hu : f (x ⊔ x') ≠ ⊤ := fun h => hlt (by rw [h, top_add])
  have hw : f (x ⊓ x') ≠ ⊤ := fun h => hlt (by rw [h, add_top])
  obtain ⟨u, hu'⟩ := WithTop.ne_top_iff_exists.1 hu
  obtain ⟨w, hw'⟩ := WithTop.ne_top_iff_exists.1 hw
  rw [← hu', ← hw', ← WithTop.coe_add] at hs
  have hs' : u + w ≤ r + r' := WithTop.coe_le_coe.1 hs
  have m1 := p2m_f79_mem f (y ⊔ z) (x ⊔ x')
  have m2 := p2m_f79_mem f (y ⊓ z) (x ⊓ x')
  rw [← hu', p2m_f79_toE] at m1
  rw [← hw', p2m_f79_toE] at m2
  rw [← hr, ← hr', p2m_f79_toE, p2m_f79_toE]
  refine le_trans ?_ (add_le_add m1 m2)
  have hp := p2m_f79_pair y z x x'
  rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

end DiscreteConvex.ConjugacyDuality

open DiscreteConvex.ConjugacyDuality in
theorem solution {V : Type*} [Fintype V] (f : (V → ℝ) → WithTop ℝ)
    (hf : SubmodularR f) :
    SupermodularEReal (ConvexConjugateR f) := by
  intro y z
  apply EReal.add_le_of_forall_lt
  intro a ha b hb
  unfold ConvexConjugateR at ha hb
  obtain ⟨s1, ⟨x, rfl⟩, h1⟩ := lt_sSup_iff.1 ha
  obtain ⟨s2, ⟨x', rfl⟩, h2⟩ := lt_sSup_iff.1 hb
  exact le_trans (add_le_add h1.le h2.le) (p2m_f79_key f hf y z x x')
