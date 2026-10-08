-- Prove2me | solution 1 for BregmanRelax.EqConstr.z_invariant
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:59:24.459389+00:00
-- url     : https://prove2.me/submissions/d1a8a5c7-620f-4218-9036-2ea2d054153f

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_EqConstr_Program



namespace BregmanRelax.EqConstr

open Filter Topology

lemma br_dir_deriv {p : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ} {G y v : EuclideanSpace ℝ (Fin p)}
    (hf : HasGradientWithinAt f G S y) (hy : S ∈ 𝓝 y) :
    HasDerivAt (fun t : ℝ => f (y + t • v)) (inner ℝ G v) 0 := by
  have hF : HasFDerivAt f (InnerProductSpace.toDual ℝ _ G) y :=
    (hasGradientWithinAt_iff_hasFDerivWithinAt.mp hf).hasFDerivAt hy
  have hl : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
    simpa using this
  have := hF.comp_hasDerivAt_of_eq (0:ℝ) hl (by simp)
  simp only [InnerProductSpace.toDual_apply_apply] at this
  exact this

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

lemma br_span {p : ℕ} (A w : EuclideanSpace ℝ (Fin p))
    (h : ∀ v, inner ℝ A v = (0:ℝ) → inner ℝ w v = (0:ℝ)) : ∃ lam : ℝ, w = lam • A := by
  by_cases hA : A = 0
  · refine ⟨0, ?_⟩
    have := h w (by simp [hA])
    rw [real_inner_self_eq_norm_sq] at this
    have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    simp [norm_eq_zero.mp this]
  · set lam : ℝ := inner ℝ A w / ‖A‖ ^ 2 with hlam
    refine ⟨lam, ?_⟩
    have hA2 : ‖A‖ ^ 2 ≠ 0 := by positivity
    have hv : inner ℝ A (w - lam • A) = (0:ℝ) := by
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hlam]
      field_simp; ring
    have h1 := h _ hv
    have h2 : inner ℝ (w - lam • A) (w - lam • A) = (0:ℝ) := by
      rw [inner_sub_left, h1, inner_smul_left, hv]; simp
    rw [real_inner_self_eq_norm_sq] at h2
    have : ‖w - lam • A‖ = 0 := by nlinarith [norm_nonneg (w - lam • A)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem lagrange_core {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S) :
    ∀ i, ∀ x ∈ interior S, ∃ lam : ℝ,
      g (P i x) = g x + lam • a i ∧ inner ℝ (a i) (P i x) = b i := by
  intro i x hx
  have hxS : x ∈ S := interior_subset hx
  obtain ⟨⟨hyH, hyS⟩, hmin⟩ := hA.proj i x hxS
  have hyint := hint i x hx
  set y := P i x with hy
  have hSn : S ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp hyint
  have horth : ∀ v, inner ℝ (a i) v = (0:ℝ) → inner ℝ (g y - g x) v = (0:ℝ) := by
    intro v hv
    have hd := br_dir_deriv (v := v) (hfg y hyS) hSn
    have hd2 : HasDerivAt (fun t : ℝ => bregmanD f g (y + t • v) x)
        (inner ℝ (g y) v - inner ℝ (g x) v) 0 := by
      have e : (fun t : ℝ => bregmanD f g (y + t • v) x) =
          fun t => f (y + t • v) - (f x + inner ℝ (g x) (y - x)) - t * inner ℝ (g x) v := by
        funext t
        simp only [bregmanD]
        have : y + t • v - x = (y - x) + t • v := by abel
        rw [this, inner_add_right, inner_smul_right]; ring
      rw [e]
      have := (hd.sub_const (f x + inner ℝ (g x) (y - x))).sub
        ((hasDerivAt_id (0:ℝ)).mul_const (inner ℝ (g x) v))
      exact this.congr_deriv (by ring)
    have hloc : IsLocalMin (fun t : ℝ => bregmanD f g (y + t • v) x) 0 := by
      have hc : Tendsto (fun t : ℝ => y + t • v) (𝓝 0) (𝓝 y) := by
        have : Continuous (fun t : ℝ => y + t • v) := by fun_prop
        simpa using this.tendsto 0
      filter_upwards [hc hSn] with t ht
      simp only [zero_smul, add_zero]
      apply hmin
      refine ⟨?_, ht⟩
      show inner ℝ (a i) (y + t • v) = b i
      rw [inner_add_right, inner_smul_right, hv, hyH.symm]; simp
    have := hloc.hasDerivAt_eq_zero hd2
    rw [inner_sub_left]; exact this
  obtain ⟨lam, hl⟩ := br_span (a i) (g y - g x) horth
  exact ⟨lam, by rw [← hl]; abel, hyH⟩

theorem zinv_core {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S) :
    ∀ i, ∀ x ∈ Zset S g a ∩ interior S, P i x ∈ Zset S g a ∩ interior S := by
  intro i x ⟨⟨hxS, u, hu⟩, hx⟩
  obtain ⟨lam, hl, -⟩ := lagrange_core hfg hA hint i x hx
  refine ⟨⟨interior_subset (hint i x hx), fun j => u j + if j = i then lam else 0, ?_⟩, hint i x hx⟩
  rw [hl, hu]
  simp [add_smul, Finset.sum_add_distrib, ite_smul]

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
    | succ n ih => rw [hx.2 n]; exact zinv_core hfg hA hint _ _ ih
  have hcl : x' ∈ closure (Zset S g a) :=
    mem_closure_of_tendsto hlim (Eventually.of_forall fun n => (hall n).1)
  exact lemma3_core hfc hfg hfcl h2 x' hx'R hcl

end BregmanRelax.EqConstr

open BregmanRelax.EqConstr
open Filter Topology

theorem solution {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S) :
    ∀ i, ∀ x ∈ Zset S g a ∩ interior S, P i x ∈ Zset S g a ∩ interior S := by
  exact zinv_core hfg hA hint
