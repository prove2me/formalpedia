-- Prove2me | solution 1 for EReal.exists_real_gt_of_average_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:51:44.855733+00:00
-- url     : https://prove2.me/submissions/5bb32112-a156-4ef5-aa67-194246c53dc3

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting
import Definitions.Def_WassDDRO_Reduction_Setting

-- carved verbatim out of submission 9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 2604-2651

section
set_option autoImplicit false
open Filter Topology
open WassDDRO.Reduction

lemma ereal_sum_ne_top {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊤) : (∑ i ∈ s, f i) ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact EReal.add_ne_top (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma tendsto_ereal_finset_sum {α ι : Type*} (F : Filter α) (s : Finset ι)
    (f : ι → α → EReal) (a : ι → EReal)
    (ha : ∀ i ∈ s, a i ≠ ⊤) (hf : ∀ i ∈ s, Tendsto (f i) F (𝓝 (a i))) :
    Tendsto (fun x => ∑ i ∈ s, f i x) F (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : EReal)) F (𝓝 0))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hs := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hc := EReal.continuousAt_add (p:=(a i, ∑ j ∈ s, a j)) (.inl (ha i (Finset.mem_insert_self _ _)))
      (.inr (ereal_sum_ne_top s a (fun j hj => ha j (Finset.mem_insert_of_mem hj))))
    exact hc.tendsto.comp ((hf i (Finset.mem_insert_self _ _)).prodMk_nhds hs)

end

section
set_option autoImplicit false
open Filter Topology

theorem solution {N : ℕ} (a : Fin N → EReal)
    (hne_top : ∀ i, a i ≠ ⊤) (r : ℝ)
    (hr : ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, a i) < (r : EReal)) :
    ∃ s : Fin N → ℝ, (∀ i, a i < (s i : EReal)) ∧ (1/(N : ℝ))*∑ i, s i < r := by
  classical
  let s : Fin N → ℕ → ℝ := fun i n => if a i=⊥ then -(n : ℝ) else (a i).toReal+1/(n+1)
  have hscore : ∀ i n, a i < (s i n : EReal) := by
    intro i n
    by_cases hb : a i=⊥
    · simpa only [s,if_pos hb,hb] using EReal.bot_lt_coe (-(n : ℝ))
    · dsimp only [s]
      rw [if_neg hb,←EReal.coe_toReal (hne_top i) hb]
      apply EReal.coe_lt_coe_iff.mpr
      simpa using (Nat.one_div_pos_of_nat (n:=n) : (0 : ℝ)<1/(n+1))
  have ht : ∀ i, Tendsto (fun n => (s i n : EReal)) atTop (𝓝 (a i)) := by
    intro i
    by_cases hb : a i=⊥
    · simp only [s,hb,if_pos]
      exact EReal.tendsto_coe_nhds_bot_iff.mpr
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
    · simp only [s,if_neg hb]
      rw [←EReal.coe_toReal (hne_top i) hb]
      apply continuous_coe_real_ereal.continuousAt.tendsto.comp
      simpa using (tendsto_const_nhds (x:=(a i).toReal)).add
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hsum := tendsto_ereal_finset_sum atTop Finset.univ
    (fun i n => (s i n : EReal)) a (fun i _ => hne_top i) (fun i _ => ht i)
  have hav := EReal.Tendsto.const_mul (a:=((1/(N : ℝ) : ℝ) : EReal)) hsum
    (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
  have hev : ∀ᶠ n : ℕ in atTop,
      ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, (s i n : EReal)) < (r : EReal) :=
    hav.eventually (isOpen_Iio.mem_nhds hr)
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨fun i => s i n,fun i => hscore i n,?_⟩
  have hs : (∑ i, (s i n : EReal)) = ((∑ i, s i n : ℝ) : EReal) :=
    (map_sum (⟨⟨Real.toEReal,EReal.coe_zero⟩,EReal.coe_add⟩ : ℝ →+ EReal) _ _).symm
  rw [hs,←EReal.coe_mul] at hn
  exact EReal.coe_lt_coe_iff.mp hn

end
