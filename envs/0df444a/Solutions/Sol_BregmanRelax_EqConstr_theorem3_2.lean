-- Prove2me | solution 2 for BregmanRelax.EqConstr.theorem3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:49.058738+00:00
-- url     : https://prove2.me/submissions/a9ebecad-6ce8-4c2f-86ae-2fc4f9cfee6b

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_EqConstr_Program
import Theorems.Thm_BregmanRelax_EqConstr_z_invariant

-- carved verbatim out of submission dd6b4728-2134-43cc-8ed6-88b46f307c8c, lines 227-247

section
open BregmanRelax
open BregmanRelax.EqConstr
open Filter Topology

lemma br_grad_ineq {p : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ} {G z x : EuclideanSpace ℝ (Fin p)}
    (hfc : ConvexOn ℝ S f) (hz : z ∈ S) (hx : x ∈ S)
    (hf : HasGradientWithinAt f G S z) :
    f z + inner ℝ G (x - z) ≤ f x := by
  have hF : HasFDerivWithinAt f (InnerProductSpace.toDual ℝ _ G) S z :=
    hasGradientWithinAt_iff_hasFDerivWithinAt.mp hf
  have hl : HasDerivWithinAt (fun t : ℝ => z + t • (x - z)) (x - z) (Set.Icc 0 1) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const (x - z)).const_add z
    simpa using this.hasDerivWithinAt
  have hmap : Set.MapsTo (fun t : ℝ => z + t • (x - z)) (Set.Icc 0 1) S := by
    intro t ht
    have := hfc.1.add_smul_sub_mem hz hx ht
    simpa using this
  have hd := hF.comp_hasDerivWithinAt_of_eq (0:ℝ) hl hmap (by simp)
  simp only [Function.comp_def, InnerProductSpace.toDual_apply_apply] at hd
  rw [hasDerivWithinAt_iff_tendsto_slope] at hd
  have hle : ∀ᶠ t in 𝓝[Set.Icc (0:ℝ) 1 \ {0}] 0,
      slope (fun t : ℝ => f (z + t • (x - z))) 0 t ≤ f x - f z := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨⟨h0, h1⟩, hne⟩ := ht
    have htpos : 0 < t := lt_of_le_of_ne h0 (Ne.symm hne)
    have hconv := hfc.2 hz hx (by linarith : (0:ℝ) ≤ 1 - t) h0 (by ring)
    have heq : (1 - t) • z + t • x = z + t • (x - z) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at hconv
    rw [slope_def_field]
    simp only [zero_smul, add_zero, sub_zero]
    rw [div_le_iff₀ htpos]
    nlinarith
  have : (𝓝[Set.Icc (0:ℝ) 1 \ {0}] (0:ℝ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    have : Set.Ioc (0:ℝ) 1 ⊆ Set.Icc 0 1 \ {0} := fun t ht =>
      ⟨⟨ht.1.le, ht.2⟩, ne_of_gt ht.1⟩
    apply closure_mono this
    rw [closure_Ioc (by norm_num)]
    simp
  have := le_of_tendsto hd hle
  linarith

lemma br_grad_ineq_cl {p : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ} {G z x : EuclideanSpace ℝ (Fin p)}
    (hfc : ConvexOn ℝ S f) (hz : z ∈ S) (hx : x ∈ closure S)
    (hfcl : ContinuousOn f (closure S))
    (hf : HasGradientWithinAt f G S z) :
    f z + inner ℝ G (x - z) ≤ f x := by
  apply ContinuousWithinAt.closure_le (f := fun w => f z + inner ℝ G (w - z)) (g := f) hx
  · exact (Continuous.continuousWithinAt (by fun_prop))
  · exact ((hfcl x hx).mono subset_closure)
  · intro w hw; exact br_grad_ineq hfc hz hw hf

theorem lemma3_core {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    (hfc : StrictConvexOn ℝ S f)
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    (hfcl : ContinuousOn f (closure S))
    (h2 : Cond2 S (bregmanD f g))
    (y' : EuclideanSpace ℝ (Fin p)) (hyR : y' ∈ feasibleEq a b S)
    (hyZ : y' ∈ closure (Zset S g a)) :
    ∀ x ∈ feasibleEq a b S, f y' ≤ f x := by
  intro x hxR
  obtain ⟨z, hzZ, hzlim⟩ := mem_closure_iff_seq_limit.mp hyZ
  have hzS : ∀ n, z n ∈ S := fun n => (hzZ n).1
  have hD := h2 z y' hzS hyR.2 hzlim
  -- key identity
  have key : ∀ n, f x - f y' = bregmanD f g x (z n) - bregmanD f g y' (z n) := by
    intro n
    obtain ⟨u, hu⟩ := (hzZ n).2
    have h0 : inner ℝ (g (z n)) (x - y') = (0:ℝ) := by
      rw [hu, sum_inner]
      apply Finset.sum_eq_zero
      intro j _
      rw [inner_smul_left, inner_sub_right, hxR.1 j, hyR.1 j]
      simp
    have : inner ℝ (g (z n)) (x - z n) = inner ℝ (g (z n)) (x - y') +
        inner ℝ (g (z n)) (y' - z n) := by
      rw [← inner_add_right]; congr 1; abel
    simp only [bregmanD]
    rw [this, h0]; ring
  have hnn : ∀ n, 0 ≤ bregmanD f g x (z n) := by
    intro n
    have := br_grad_ineq_cl hfc.convexOn (hzS n) hxR.2 hfcl (hfg _ (hzS n))
    simp only [bregmanD]; linarith
  have hlow : ∀ n, -bregmanD f g y' (z n) ≤ f x - f y' := by
    intro n; rw [key n]; linarith [hnn n]
  have := le_of_tendsto (hD.neg) (Eventually.of_forall hlow)
  simp at this
  linarith

theorem theorem3_core {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hfc : StrictConvexOn ℝ S f)
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    (hfcl : ContinuousOn f (closure S))
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (h2 : Cond2 S (bregmanD f g))
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S)
    (i : ℕ → Fin m) (x : ℕ → EuclideanSpace ℝ (Fin p)) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x)
    (hx0 : x 0 ∈ Zset S g a ∩ interior S)
    (x' : EuclideanSpace ℝ (Fin p)) (hlim : Filter.Tendsto x Filter.atTop (nhds x'))
    (hx'R : x' ∈ feasibleEq a b S) :
    ∀ y ∈ feasibleEq a b S, f x' ≤ f y := by
  have hall : ∀ n, x n ∈ Zset S g a ∩ interior S := by
    intro n
    induction n with
    | zero => exact hx0
    | succ n ih => rw [hx.2 n]; exact BregmanRelax.EqConstr.z_invariant hfg hA hint _ _ ih
  have hcl : x' ∈ closure (Zset S g a) :=
    mem_closure_of_tendsto hlim (Eventually.of_forall fun n => (hall n).1)
  exact lemma3_core hfc hfg hfcl h2 x' hx'R hcl

end

section
open BregmanRelax.EqConstr
open Filter Topology

theorem solution {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hS : Convex ℝ S) (hfc : StrictConvexOn ℝ S f)
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x) (hgc : ContinuousOn g S)
    (hfcl : ContinuousOn f (closure S))
    (ha : ∀ i, a i ≠ 0)
    (hRne : (feasibleEq a b S).Nonempty)
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (hV : BregmanRelax.Cyclic.CondV S (bregmanD f g) (feasibleEq a b S ∩ S))
    (h2 : Cond2 S (bregmanD f g))
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S)
    (i : ℕ → Fin m) (x : ℕ → EuclideanSpace ℝ (Fin p)) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x)
    (hx0 : x 0 ∈ Zset S g a ∩ interior S)
    (x' : EuclideanSpace ℝ (Fin p)) (hlim : Filter.Tendsto x Filter.atTop (nhds x'))
    (hx'R : x' ∈ feasibleEq a b S) :
    ∀ y ∈ feasibleEq a b S, f x' ≤ f y := by
  exact theorem3_core hfc hfg hfcl hA h2 hint i x hx hx0 x' hlim hx'R

end
