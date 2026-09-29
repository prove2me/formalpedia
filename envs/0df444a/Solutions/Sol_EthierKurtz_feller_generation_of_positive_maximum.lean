-- Prove2me | solution 1 for EthierKurtz.feller_generation_of_positive_maximum
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T20:05:57.385286+00:00
-- url     : https://prove2.me/submissions/30b967ca-d069-418b-bed9-2cdfea551a48

import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter NormedSpace
open scoped Topology BigOperators

namespace EthierKurtz.FellerProof

open EthierKurtz

section General

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The positive maximum principle implies dissipativity. -/
theorem dissipative_of_pmp (G : Submodule ℝ (C(X, ℝ) × C(X, ℝ)))
    (hpmp : ∀ fg ∈ G, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0)
    (r : ℝ) : ∀ p ∈ G, r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖ := by
  intro p hp
  rcases isEmpty_or_nonempty X with hX | hX
  · have : p.1 = 0 := Subsingleton.elim _ _
    simp [this]
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_norm.comp p.1.continuous).continuousOn
  have hnorm : ‖p.1‖ = |p.1 x| :=
    le_antisymm ((ContinuousMap.norm_le _ (abs_nonneg _)).2 fun y => hx (Set.mem_univ y))
      (p.1.norm_coe_le_norm x)
  have key : ∀ q ∈ G, q.1 x = ‖q.1‖ → r * ‖q.1‖ ≤ ‖r • q.1 - q.2‖ := by
    intro q hq hqx
    have hmax : ∀ y, q.1 y ≤ q.1 x := fun y => hqx ▸ q.1.apply_le_norm y
    have h2 := hpmp q hq x hmax (hqx ▸ norm_nonneg _)
    calc r * ‖q.1‖ ≤ r * q.1 x - q.2 x := by rw [hqx]; linarith
      _ = (r • q.1 - q.2) x := by simp
      _ ≤ ‖r • q.1 - q.2‖ := ContinuousMap.apply_le_norm _ _
  rcases le_or_gt 0 (p.1 x) with h | h
  · exact key p hp (by rw [hnorm, abs_of_nonneg h])
  · have := key (-p) (G.neg_mem hp) (by simp [hnorm, abs_of_neg h])
    have e : r • (-p).1 - (-p).2 = -(r • p.1 - p.2) := by simp [smul_neg]; abel
    rw [e, norm_neg] at this
    simpa using this

/-- The positive maximum principle implies dissipativity on the closure. -/
theorem dissipative_closure_of_pmp (G : Submodule ℝ (C(X, ℝ) × C(X, ℝ)))
    (hpmp : ∀ fg ∈ G, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0)
    (r : ℝ) :
    ∀ p ∈ closure (G : Set (C(X, ℝ) × C(X, ℝ))), r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖ := by
  have hcl : IsClosed {p : C(X, ℝ) × C(X, ℝ) | r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖} :=
    isClosed_le (continuous_const.mul (continuous_norm.comp continuous_fst))
      (continuous_norm.comp ((continuous_fst.const_smul r).sub continuous_snd))
  exact closure_minimal (fun p hp => dissipative_of_pmp G hpmp r p hp) hcl

end General


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `ℚ`-algebra structure on bounded operators, needed to form operator exponentials. -/
noncomputable def normedAlgebraRatCLM : NormedAlgebra ℚ (E →L[ℝ] E) :=
  NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)

attribute [local instance] normedAlgebraRatCLM

section Density

/-- Pointwise convergence of uniformly bounded operators on a dense set extends to
all vectors. -/
theorem tendsto_of_dense_of_bound {ι : Type*} {l : Filter ι} {D : Set E} (hD : Dense D)
    (L : ι → E →L[ℝ] E) (M : E →L[ℝ] E) (C : ℝ) (hb : ∀ᶠ i in l, ‖L i‖ ≤ C)
    (h : ∀ d ∈ D, Tendsto (fun i => L i d) l (𝓝 (M d))) (f : E) :
    Tendsto (fun i => L i f) l (𝓝 (M f)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K := max C 0 + ‖M‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨d, hdD, hd⟩ := hD.exists_dist_lt f (show 0 < ε / (2 * K) by positivity)
  filter_upwards [hb, Metric.tendsto_nhds.1 (h d hdD) (ε / 2) (by positivity)] with i hi hi2
  have e : L i f - M f = L i (f - d) + (L i d - M d) + M (d - f) := by
    simp only [map_sub]; abel
  rw [dist_eq_norm, e]
  rw [dist_eq_norm] at hd hi2
  have h1 : ‖L i (f - d)‖ ≤ max C 0 * ‖f - d‖ :=
    ((L i).le_opNorm _).trans (by gcongr; exact hi.trans (le_max_left _ _))
  have h2 : ‖M (d - f)‖ ≤ ‖M‖ * ‖f - d‖ :=
    (M.le_opNorm _).trans (by rw [norm_sub_rev])
  have h3 : (max C 0 + ‖M‖) * ‖f - d‖ < ε / 2 := by
    calc (max C 0 + ‖M‖) * ‖f - d‖ ≤ K * ‖f - d‖ := by gcongr; linarith
      _ < K * (ε / (2 * K)) := by gcongr
      _ = ε / 2 := by field_simp
  calc ‖L i (f - d) + (L i d - M d) + M (d - f)‖
      ≤ ‖L i (f - d)‖ + ‖L i d - M d‖ + ‖M (d - f)‖ := norm_add₃_le
    _ < ε := by nlinarith

/-- Cauchy sequences of uniformly bounded operators on a dense set. -/
theorem cauchySeq_of_dense_of_bound {D : Set E} (hD : Dense D)
    (L : ℕ → E →L[ℝ] E) (C : ℝ) (hb : ∀ n, ‖L n‖ ≤ C)
    (h : ∀ d ∈ D, CauchySeq (fun n => L n d)) (f : E) :
    CauchySeq (fun n => L n f) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  set K := max C 0 + 1 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨d, hdD, hd⟩ := hD.exists_dist_lt f (show 0 < ε / (3 * K) by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (h d hdD) (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hb' : ∀ k, ‖L k (f - d)‖ ≤ K * ‖f - d‖ := fun k =>
    ((L k).le_opNorm _).trans (by
      gcongr; exact (hb k).trans (by rw [hK]; linarith [le_max_left C 0]))
  have e : L m f - L n f = L m (f - d) + (L m d - L n d) - L n (f - d) := by
    simp only [map_sub]; abel
  have hN' := hN m hm n hn
  rw [dist_eq_norm] at hd hN' ⊢
  rw [e]
  have h3 : K * ‖f - d‖ < ε / 3 := by
    calc K * ‖f - d‖ < K * (ε / (3 * K)) := by gcongr
      _ = ε / 3 := by field_simp
  calc ‖L m (f - d) + (L m d - L n d) - L n (f - d)‖
      ≤ ‖L m (f - d)‖ + ‖L m d - L n d‖ + ‖L n (f - d)‖ :=
        norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ < ε := by linarith [hb' m, hb' n]

/-- `‖exp B‖ ≤ exp ‖B‖` for bounded operators. -/
theorem norm_exp_clm_le (B : E →L[ℝ] E) : ‖exp B‖ ≤ Real.exp ‖B‖ := by
  have hle : ∀ k : ℕ, ‖((k.factorial : ℝ)⁻¹) • B ^ k‖ ≤ ‖B‖ ^ k / k.factorial := by
    intro k
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_eq_inv_mul]
    gcongr
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
    · exact norm_pow_le' B hk
  have hs : Summable fun k : ℕ => ‖B‖ ^ k / k.factorial := Real.summable_pow_div_factorial _
  have hs' : Summable fun k : ℕ => ‖((k.factorial : ℝ)⁻¹) • B ^ k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs
  rw [NormedSpace.exp_eq_tsum ℝ, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact (norm_tsum_le_tsum_norm hs').trans (hs'.tsum_le_tsum hle hs)

theorem exp_smul_one_clm (a : ℝ) : exp (a • (1 : E →L[ℝ] E)) = Real.exp a • 1 := by
  rw [Real.exp_eq_exp_ℝ, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
    NormedSpace.algebraMap_exp_comm]

end Density

/-- The data of a generator: a closed dissipative linear relation with dense domain
such that `r - A` is surjective for all `r > 0`. -/
structure HYGen (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  A : Submodule ℝ (E × E)
  closed : IsClosed (A : Set (E × E))
  diss : ∀ p ∈ A, ∀ r : ℝ, 0 < r → r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖
  surj : ∀ r : ℝ, 0 < r → ∀ h : E, ∃ p ∈ A, r • p.1 - p.2 = h
  dense : Dense (Prod.fst '' (A : Set (E × E)))

namespace HYGen

variable (G : HYGen E)

theorem eq_of_sub_eq {r : ℝ} (hr : 0 < r) {p q : E × E} (hp : p ∈ G.A) (hq : q ∈ G.A)
    (h : r • p.1 - p.2 = r • q.1 - q.2) : p = q := by
  have hd := G.diss (p - q) (G.A.sub_mem hp hq) r hr
  have e : r • (p - q).1 - (p - q).2 = 0 := by
    simp only [Prod.fst_sub, Prod.snd_sub, smul_sub]
    rw [← sub_eq_zero] at h; rw [← h]; abel
  rw [e, norm_zero] at hd
  have h1 : (p - q).1 = 0 :=
    norm_eq_zero.1 (le_antisymm (by nlinarith [norm_nonneg (p - q).1]) (norm_nonneg _))
  have h1' : p.1 = q.1 := sub_eq_zero.1 h1
  have h2 : p.2 = q.2 := by rw [h1'] at h; exact sub_right_injective h
  exact Prod.ext h1' h2

/-- The resolvent as a function. -/
noncomputable def resFun (r : ℝ) (h : E) : E := by
  classical
  exact if H : ∃ p ∈ G.A, r • p.1 - p.2 = h then (Classical.choose H).1 else 0

theorem resFun_mem {r : ℝ} (hr : 0 < r) (h : E) :
    (G.resFun r h, r • G.resFun r h - h) ∈ G.A := by
  have H := G.surj r hr h
  have hdef : G.resFun r h = (Classical.choose H).1 := by
    unfold resFun; rw [dif_pos H]
  obtain ⟨hm, he⟩ := Classical.choose_spec H
  rw [hdef]
  generalize Classical.choose H = p at hm he ⊢
  subst he
  convert hm using 1
  ext
  · rfl
  · simp

theorem resFun_eq {r : ℝ} (hr : 0 < r) {u h : E} (hu : (u, r • u - h) ∈ G.A) :
    G.resFun r h = u := by
  have := G.eq_of_sub_eq hr (G.resFun_mem hr h) hu (by simp)
  exact congrArg Prod.fst this

theorem norm_resFun_le {r : ℝ} (hr : 0 < r) (h : E) : ‖G.resFun r h‖ ≤ (1 / r) * ‖h‖ := by
  have := G.diss _ (G.resFun_mem hr h) r hr
  simp only [sub_sub_cancel] at this
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hr]; linarith

/-- The resolvent `(r - A)⁻¹` as a bounded operator (zero for `r ≤ 0`). -/
noncomputable def res (r : ℝ) : E →L[ℝ] E := by
  classical
  exact if hr : 0 < r then
    LinearMap.mkContinuous
      { toFun := G.resFun r
        map_add' := fun h k => by
          refine G.resFun_eq hr ?_
          have := G.A.add_mem (G.resFun_mem hr h) (G.resFun_mem hr k)
          convert this using 1
          ext <;> simp [smul_add]; abel
        map_smul' := fun a h => by
          refine G.resFun_eq hr ?_
          have := G.A.smul_mem a (G.resFun_mem hr h)
          convert this using 1
          ext <;> simp [smul_sub, smul_comm r a] }
      (1 / r) (G.norm_resFun_le hr)
  else 0

theorem res_apply {r : ℝ} (hr : 0 < r) (h : E) : G.res r h = G.resFun r h := by
  simp [res, hr]

theorem res_mem {r : ℝ} (hr : 0 < r) (h : E) : (G.res r h, r • G.res r h - h) ∈ G.A := by
  rw [G.res_apply hr]; exact G.resFun_mem hr h

theorem res_eq {r : ℝ} (hr : 0 < r) {u h : E} (hu : (u, r • u - h) ∈ G.A) :
    G.res r h = u := by
  rw [G.res_apply hr]; exact G.resFun_eq hr hu

theorem res_of_mem {r : ℝ} (hr : 0 < r) {p : E × E} (hp : p ∈ G.A) :
    G.res r (r • p.1 - p.2) = p.1 :=
  G.res_eq hr (by simpa using hp)

theorem norm_res_le {r : ℝ} (hr : 0 < r) : ‖G.res r‖ ≤ 1 / r := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [G.res_apply hr]; exact G.norm_resFun_le hr h

theorem res_ident {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (h : E) :
    G.res r h = G.res s h + (s - r) • G.res r (G.res s h) := by
  refine G.res_eq hr ?_
  have := G.A.add_mem (G.res_mem hs h) (G.A.smul_mem (s - r) (G.res_mem hr (G.res s h)))
  convert this using 1
  ext
  · simp
  · simp only [Prod.snd_add, Prod.smul_snd]; module

theorem res_commute {r s : ℝ} (hr : 0 < r) (hs : 0 < s) : Commute (G.res r) (G.res s) := by
  rcases eq_or_ne r s with rfl | hne
  · exact Commute.refl _
  ext h
  have h1 := G.res_ident hr hs h
  have h2 := G.res_ident hs hr h
  have : (s - r) • (G.res r (G.res s h) - G.res s (G.res r h)) = 0 := by
    linear_combination (norm := module) -h1 - h2
  rw [smul_eq_zero] at this
  rcases this with h0 | h0
  · exact absurd (sub_eq_zero.1 h0).symm hne
  · simpa [ContinuousLinearMap.mul_apply] using sub_eq_zero.1 h0

theorem smul_res_of_mem {r : ℝ} (hr : 0 < r) {p : E × E} (hp : p ∈ G.A) :
    r • G.res r p.1 = p.1 + G.res r p.2 := by
  have := G.res_of_mem hr hp
  rw [map_sub, map_smul] at this
  conv_rhs => rw [← this]
  abel

theorem tendsto_smul_res (g : E) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1) • G.res ((n : ℝ) + 1)) g) atTop (𝓝 g) := by
  refine tendsto_of_dense_of_bound G.dense _ (ContinuousLinearMap.id ℝ E) 1
    (Eventually.of_forall fun n => ?_) ?_ g
  · have hn : (0 : ℝ) < n + 1 := by positivity
    rw [norm_smul, Real.norm_of_nonneg hn.le]
    calc ((n : ℝ) + 1) * ‖G.res ((n : ℝ) + 1)‖ ≤ ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := by
          gcongr; exact G.norm_res_le hn
      _ = 1 := by field_simp
  · rintro _ ⟨p, hp, rfl⟩
    have key : ∀ n : ℕ, (((n : ℝ) + 1) • G.res ((n : ℝ) + 1)) p.1 =
        p.1 + G.res ((n : ℝ) + 1) p.2 := fun n =>
      G.smul_res_of_mem (by positivity) hp
    simp only [key, ContinuousLinearMap.id_apply]
    conv => rhs; rw [← add_zero p.1]
    refine tendsto_const_nhds.add ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n : ℕ => 1 / ((n : ℝ) + 1) * ‖p.2‖) (fun _ => norm_nonneg _)
      (fun n => ?_) (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖p.2‖))
    have hn : (0 : ℝ) < n + 1 := by positivity
    exact ((G.res _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (G.norm_res_le hn) (norm_nonneg _))

/-- The Yosida approximation `Aₙ = (n+1)² R_{n+1} - (n+1)`. -/
noncomputable def yos (n : ℕ) : E →L[ℝ] E :=
  (((n : ℝ) + 1) ^ 2) • G.res ((n : ℝ) + 1) - ((n : ℝ) + 1) • 1

theorem yos_apply_of_mem (n : ℕ) {p : E × E} (hp : p ∈ G.A) :
    G.yos n p.1 = ((n : ℝ) + 1) • G.res ((n : ℝ) + 1) p.2 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have := G.smul_res_of_mem hn hp
  simp only [yos, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
  rw [pow_two, mul_smul, this, smul_add]; abel

theorem tendsto_yos {p : E × E} (hp : p ∈ G.A) :
    Tendsto (fun n => G.yos n p.1) atTop (𝓝 p.2) := by
  simp only [G.yos_apply_of_mem _ hp]
  exact G.tendsto_smul_res p.2

theorem yos_commute (n m : ℕ) : Commute (G.yos n) (G.yos m) := by
  have hc := G.res_commute (r := (n : ℝ) + 1) (s := (m : ℝ) + 1) (by positivity) (by positivity)
  unfold yos
  refine Commute.sub_left (Commute.sub_right ?_ ?_) (Commute.sub_right ?_ ?_)
  · exact (hc.smul_left _).smul_right _
  · exact ((Commute.one_right _).smul_left _).smul_right _
  · exact ((Commute.one_left _).smul_left _).smul_right _
  · exact ((Commute.one_left _).smul_left _).smul_right _

variable [CompleteSpace E]

/-- The approximating semigroups `exp (t • Aₙ)`. -/
noncomputable def sgn (n : ℕ) (t : ℝ) : E →L[ℝ] E := exp (t • G.yos n)

theorem sgn_eq (n : ℕ) (t : ℝ) :
    G.sgn n t = Real.exp (-(t * ((n : ℝ) + 1))) •
      exp ((t * ((n : ℝ) + 1) ^ 2) • G.res ((n : ℝ) + 1)) := by
  have e : t • G.yos n = (-(t * ((n : ℝ) + 1))) • (1 : E →L[ℝ] E) +
      (t * ((n : ℝ) + 1) ^ 2) • G.res ((n : ℝ) + 1) := by
    unfold yos; rw [smul_sub, smul_smul, smul_smul]; module
  rw [sgn, e, exp_add_of_commute ((Commute.one_left _).smul_left _), exp_smul_one_clm,
    smul_mul_assoc, one_mul]

theorem sgn_hasSum (n : ℕ) (t : ℝ) (f : E) :
    HasSum (fun k : ℕ => (Real.exp (-(t * ((n : ℝ) + 1))) *
      ((k.factorial : ℝ)⁻¹ * (t * ((n : ℝ) + 1) ^ 2) ^ k)) • ((G.res ((n : ℝ) + 1)) ^ k) f)
      (G.sgn n t f) := by
  set B := (t * ((n : ℝ) + 1) ^ 2) • G.res ((n : ℝ) + 1)
  have h1 : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • B ^ k) (exp B) := by
    rw [NormedSpace.exp_eq_tsum ℝ]; exact (NormedSpace.expSeries_summable' (𝕂 := ℝ) B).hasSum
  have h2 := (h1.mapL (ContinuousLinearMap.apply ℝ E f)).const_smul
    (Real.exp (-(t * ((n : ℝ) + 1))))
  have e2 : (Real.exp (-(t * ((n : ℝ) + 1))) • exp B) f =
      Real.exp (-(t * ((n : ℝ) + 1))) • (ContinuousLinearMap.apply ℝ E f) (exp B) := rfl
  rw [sgn_eq, e2]
  convert h2 using 1
  ext k
  simp only [B, ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, smul_pow,
    smul_smul]

omit [CompleteSpace E] in
theorem sgn_zero (n : ℕ) : G.sgn n 0 = 1 := by
  simp [sgn]

theorem sgn_add (n : ℕ) (s t : ℝ) : G.sgn n (s + t) = G.sgn n s * G.sgn n t := by
  rw [sgn, add_smul, exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t)]; rfl

theorem norm_sgn_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : ‖G.sgn n t‖ ≤ 1 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [sgn_eq, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hB : ‖(t * ((n : ℝ) + 1) ^ 2) • G.res ((n : ℝ) + 1)‖ ≤ t * ((n : ℝ) + 1) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc t * ((n : ℝ) + 1) ^ 2 * ‖G.res ((n : ℝ) + 1)‖
        ≤ t * ((n : ℝ) + 1) ^ 2 * (1 / ((n : ℝ) + 1)) := by gcongr; exact G.norm_res_le hn
      _ = t * ((n : ℝ) + 1) := by field_simp
  calc Real.exp (-(t * ((n : ℝ) + 1))) * ‖exp ((t * ((n : ℝ) + 1) ^ 2) • G.res ((n : ℝ) + 1))‖
      ≤ Real.exp (-(t * ((n : ℝ) + 1))) * Real.exp (t * ((n : ℝ) + 1)) := by
        gcongr; exact (norm_exp_clm_le _).trans (Real.exp_le_exp.2 hB)
    _ = 1 := by rw [← Real.exp_add]; simp

omit [CompleteSpace E] in
theorem sgn_commute (n m : ℕ) (s t : ℝ) : Commute (G.sgn n s) (G.sgn m t) :=
  ((((G.yos_commute n m).smul_left s).smul_right t).exp_right).exp_left

omit [CompleteSpace E] in
theorem sgn_commute_yos (n m : ℕ) (s : ℝ) : Commute (G.sgn n s) (G.yos m) :=
  (((G.yos_commute n m).smul_left s)).exp_left

theorem hasDerivAt_sgn (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s => G.sgn n s) (G.sgn n t * G.yos n) t :=
  hasDerivAt_exp_smul_const (G.yos n) t

theorem norm_sgn_sub_sgn (n m : ℕ) {t : ℝ} (ht : 0 ≤ t) (f : E) :
    ‖G.sgn n t f - G.sgn m t f‖ ≤ t * ‖G.yos n f - G.yos m f‖ := by
  have hd : ∀ s, HasDerivAt (fun s => (G.sgn n (t - s) * G.sgn m s) f)
      (G.sgn n (t - s) (G.sgn m s (G.yos m f - G.yos n f))) s := by
    intro s
    have h1 := (G.hasDerivAt_sgn n (t - s)).comp_const_sub t s
    have h2 := G.hasDerivAt_sgn m s
    refine ((h1.clm_comp h2).clm_apply (hasDerivAt_const s f)).congr_deriv ?_
    have hc : G.yos n (G.sgn m s f) = G.sgn m s (G.yos n f) :=
      (congrArg (fun L : E →L[ℝ] E => L f) (G.sgn_commute_yos m n s).eq).symm
    have e1 : ((-(G.sgn n (t - s) * G.yos n)).comp (G.sgn m s)) f =
        -(G.sgn n (t - s) (G.yos n (G.sgn m s f))) := rfl
    have e2 : ((G.sgn n (t - s)).comp (G.sgn m s * G.yos m)) f =
        G.sgn n (t - s) (G.sgn m s (G.yos m f)) := rfl
    rw [ContinuousLinearMap.add_apply, e1, e2, map_zero, add_zero, hc, map_sub, map_sub]
    abel
  have := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => (G.sgn n (t - s) * G.sgn m s) f) (C := ‖G.yos m f - G.yos n f‖)
    (fun s _ => (hd s).hasDerivWithinAt) (fun s hs => ?_) t ⟨ht, le_rfl⟩
  · simp only [sub_self, G.sgn_zero, sub_zero, one_mul, mul_one] at this
    rw [norm_sub_rev, mul_comm, norm_sub_rev (G.yos n f)]; simpa using this
  · have h1 := G.norm_sgn_le n (show 0 ≤ t - s by linarith [hs.2])
    have h2 := G.norm_sgn_le m hs.1
    calc _ ≤ ‖G.sgn n (t - s)‖ * ‖G.sgn m s (G.yos m f - G.yos n f)‖ := (G.sgn n _).le_opNorm _
      _ ≤ 1 * (1 * ‖G.yos m f - G.yos n f‖) := by
        gcongr; exact ((G.sgn m s).le_opNorm _).trans (by gcongr)
      _ = _ := by ring

theorem norm_sgn_sub_self (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (f : E) :
    ‖G.sgn n t f - f‖ ≤ t * ‖G.yos n f‖ := by
  have hd : ∀ s, HasDerivAt (fun s => G.sgn n s f) (G.sgn n s (G.yos n f)) s := by
    intro s
    have := (G.hasDerivAt_sgn n s).clm_apply (hasDerivAt_const s f)
    simpa using this
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => G.sgn n s f)
    (C := ‖G.yos n f‖) (fun s _ => (hd s).hasDerivWithinAt) (fun s hs => ?_) t ⟨ht, le_rfl⟩
  · simpa [G.sgn_zero, mul_comm] using this
  · exact ((G.sgn n s).le_opNorm _).trans (by
      have := G.norm_sgn_le n hs.1
      nlinarith [norm_nonneg (G.yos n f)])

theorem norm_sgn_sub_self_sub (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (f : E) (B : ℝ)
    (hB : ∀ s ∈ Set.Icc 0 t, ‖G.sgn n s (G.yos n f) - G.yos n f‖ ≤ B) :
    ‖G.sgn n t f - f - t • G.yos n f‖ ≤ B * t := by
  have hd : ∀ s, HasDerivAt (fun s => G.sgn n s f - s • G.yos n f)
      (G.sgn n s (G.yos n f) - G.yos n f) s := by
    intro s
    refine (((G.hasDerivAt_sgn n s).clm_apply (hasDerivAt_const s f)).sub
      ((hasDerivAt_id s).smul_const (G.yos n f))).congr_deriv ?_
    have e1 : (G.sgn n s * G.yos n) f = G.sgn n s (G.yos n f) := rfl
    rw [e1, map_zero, add_zero, one_smul]
  have := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => G.sgn n s f - s • G.yos n f)
    (fun s _ => (hd s).hasDerivWithinAt) (fun s hs => hB s (Set.Ico_subset_Icc_self hs)) t
    ⟨ht, le_rfl⟩
  simp only [G.sgn_zero, zero_smul, sub_zero, ContinuousLinearMap.one_apply] at this
  convert this using 2; abel

theorem cauchySeq_sgn {t : ℝ} (ht : 0 ≤ t) (f : E) : CauchySeq (fun n => G.sgn n t f) := by
  refine cauchySeq_of_dense_of_bound G.dense (fun n => G.sgn n t) 1
    (fun n => G.norm_sgn_le n ht) ?_ f
  rintro _ ⟨p, hp, rfl⟩
  have hc := (G.tendsto_yos hp).cauchySeq
  rw [Metric.cauchySeq_iff] at hc ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε / (t + 1)) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := hN m hm n hn
  rw [dist_eq_norm] at h1 ⊢
  calc ‖G.sgn m t p.1 - G.sgn n t p.1‖ ≤ t * ‖G.yos m p.1 - G.yos n p.1‖ :=
        G.norm_sgn_sub_sgn m n ht p.1
    _ ≤ (t + 1) * ‖G.yos m p.1 - G.yos n p.1‖ := by gcongr; linarith
    _ < (t + 1) * (ε / (t + 1)) := by gcongr
    _ = ε := by field_simp

theorem tendsto_sgn_fun {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n x => G.sgn n t x) atTop
      (𝓝 (fun x => limUnder atTop (fun n => G.sgn n t x))) :=
  tendsto_pi_nhds.2 fun x => (G.cauchySeq_sgn ht x).tendsto_limUnder

/-- The limiting semigroup. -/
noncomputable def sg (t : ℝ) : E →L[ℝ] E :=
  if ht : 0 ≤ t then continuousLinearMapOfTendsto (fun n => G.sgn n t) (G.tendsto_sgn_fun ht)
  else 0

theorem tendsto_sg {t : ℝ} (ht : 0 ≤ t) (f : E) :
    Tendsto (fun n => G.sgn n t f) atTop (𝓝 (G.sg t f)) := by
  have : G.sg t f = limUnder atTop (fun n => G.sgn n t f) := by
    simp [sg, ht, continuousLinearMapOfTendsto]
  rw [this]; exact (G.cauchySeq_sgn ht f).tendsto_limUnder

theorem sg_zero : G.sg 0 = ContinuousLinearMap.id ℝ E := by
  ext f
  have := G.tendsto_sg le_rfl f
  simp only [G.sgn_zero, ContinuousLinearMap.one_apply] at this
  exact tendsto_nhds_unique this tendsto_const_nhds

theorem sg_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : G.sg (s + t) = (G.sg s).comp (G.sg t) := by
  ext f
  refine tendsto_nhds_unique (G.tendsto_sg (add_nonneg hs ht) f) ?_
  simp only [G.sgn_add, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]
  have e : ∀ n, G.sgn n s (G.sgn n t f) =
      G.sgn n s (G.sgn n t f - G.sg t f) + G.sgn n s (G.sg t f) := fun n => by
    rw [← map_add, sub_add_cancel]
  simp only [e]
  conv => rhs; rw [← zero_add (G.sg s (G.sg t f))]
  refine Tendsto.add ?_ (G.tendsto_sg hs _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h0 : Tendsto (fun n => ‖G.sgn n t f - G.sg t f‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).1 (G.tendsto_sg ht f)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
  exact ((G.sgn n s).le_opNorm _).trans (by
    have := G.norm_sgn_le n hs
    nlinarith [norm_nonneg (G.sgn n t f - G.sg t f)])

theorem norm_sg_le {t : ℝ} (ht : 0 ≤ t) : ‖G.sg t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  refine le_of_tendsto (G.tendsto_sg ht f).norm (Eventually.of_forall fun n => ?_)
  exact ((G.sgn n t).le_opNorm _).trans (by
    have := G.norm_sgn_le n ht
    nlinarith [norm_nonneg f])

theorem norm_sg_sub_self {t : ℝ} (ht : 0 ≤ t) {p : E × E} (hp : p ∈ G.A) :
    ‖G.sg t p.1 - p.1‖ ≤ t * ‖p.2‖ :=
  le_of_tendsto_of_tendsto' ((G.tendsto_sg ht p.1).sub_const p.1).norm
    ((G.tendsto_yos hp).norm.const_mul t) fun n => G.norm_sgn_sub_self n ht p.1

theorem tendsto_sg_nhds (f : E) : Tendsto (fun t => G.sg t f) (𝓝[>] 0) (𝓝 f) := by
  refine tendsto_of_dense_of_bound G.dense G.sg (ContinuousLinearMap.id ℝ E) 1
    (eventually_nhdsWithin_of_forall fun t ht => G.norm_sg_le (le_of_lt ht)) ?_ f
  rintro _ ⟨p, hp, rfl⟩
  simp only [ContinuousLinearMap.id_apply]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun t : ℝ => t * ‖p.2‖) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t * ‖p.2‖) (𝓝 0) (𝓝 (0 * ‖p.2‖)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at this; exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun t ht => G.norm_sg_sub_self (le_of_lt ht) hp) h0

theorem isSCCS : IsStronglyContinuousContractionSemigroup G.sg :=
  ⟨G.sg_zero, fun _ _ hs ht => G.sg_add hs ht, fun _ ht => G.norm_sg_le ht, G.tendsto_sg_nhds⟩

theorem norm_sg_sub_sub_le {t : ℝ} (ht : 0 ≤ t) {p q : E × E} (hp : p ∈ G.A) (hq : q ∈ G.A) :
    ‖G.sg t p.1 - p.1 - t • p.2‖ ≤ (t * ‖q.2‖ + 2 * ‖p.2 - q.1‖) * t := by
  have hbound : ∀ n, ‖G.sgn n t p.1 - p.1 - t • G.yos n p.1‖ ≤
      (t * ‖G.yos n q.1‖ + 2 * ‖p.2 - q.1‖ + 2 * ‖G.yos n p.1 - p.2‖) * t := by
    intro n
    refine G.norm_sgn_sub_self_sub n ht p.1 _ fun s hs => ?_
    set y := G.yos n p.1
    have e : G.sgn n s y - y = (G.sgn n s (y - q.1) - (y - q.1)) + (G.sgn n s q.1 - q.1) := by
      rw [map_sub]; abel
    have h1 : ‖G.sgn n s (y - q.1)‖ ≤ ‖y - q.1‖ := ((G.sgn n s).le_opNorm _).trans (by
      have := G.norm_sgn_le n hs.1
      nlinarith [norm_nonneg (y - q.1)])
    have h2 : ‖G.sgn n s q.1 - q.1‖ ≤ t * ‖G.yos n q.1‖ :=
      (G.norm_sgn_sub_self n hs.1 q.1).trans (by gcongr; exact hs.2)
    have h3 : ‖y - q.1‖ ≤ ‖y - p.2‖ + ‖p.2 - q.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [e]
    calc _ ≤ ‖G.sgn n s (y - q.1) - (y - q.1)‖ + ‖G.sgn n s q.1 - q.1‖ := norm_add_le _ _
      _ ≤ (‖G.sgn n s (y - q.1)‖ + ‖y - q.1‖) + ‖G.sgn n s q.1 - q.1‖ := by
        gcongr; exact norm_sub_le _ _
      _ ≤ _ := by linarith
  have hL : Tendsto (fun n => ‖G.sgn n t p.1 - p.1 - t • G.yos n p.1‖) atTop
      (𝓝 ‖G.sg t p.1 - p.1 - t • p.2‖) :=
    (((G.tendsto_sg ht p.1).sub_const p.1).sub ((G.tendsto_yos hp).const_smul t)).norm
  have hR : Tendsto
      (fun n => (t * ‖G.yos n q.1‖ + 2 * ‖p.2 - q.1‖ + 2 * ‖G.yos n p.1 - p.2‖) * t)
      atTop (𝓝 ((t * ‖q.2‖ + 2 * ‖p.2 - q.1‖ + 2 * 0) * t)) := by
    refine ((((G.tendsto_yos hq).norm.const_mul t).add_const _).add ?_).mul_const t
    exact ((tendsto_iff_norm_sub_tendsto_zero).1 (G.tendsto_yos hp)).const_mul 2
  have := le_of_tendsto_of_tendsto' hL hR hbound
  simpa using this

theorem tendsto_generator_of_mem {p : E × E} (hp : p ∈ G.A) :
    Tendsto (fun t : ℝ => t⁻¹ • (G.sg t p.1 - p.1)) (𝓝[>] 0) (𝓝 p.2) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨_, ⟨q, hq, rfl⟩, hqd⟩ := G.dense.exists_dist_lt p.2 (show 0 < ε / 4 by positivity)
  refine ⟨ε / (2 * (‖q.2‖ + 1)), by positivity, fun t ht htd => ?_⟩
  have ht0 : 0 < t := ht
  rw [dist_eq_norm] at hqd ⊢
  rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at htd
  have e : t⁻¹ • (G.sg t p.1 - p.1) - p.2 = t⁻¹ • (G.sg t p.1 - p.1 - t • p.2) := by
    rw [smul_sub (t⁻¹) _ (t • p.2), smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)]
  have hb := G.norm_sg_sub_sub_le ht0.le hp hq
  have h1 : t * ‖q.2‖ < ε / 2 := by
    calc t * ‖q.2‖ ≤ t * (‖q.2‖ + 1) := by gcongr; linarith
      _ < ε / (2 * (‖q.2‖ + 1)) * (‖q.2‖ + 1) := by gcongr
      _ = ε / 2 := by field_simp
  calc t⁻¹ * ‖G.sg t p.1 - p.1 - t • p.2‖ ≤ t⁻¹ * ((t * ‖q.2‖ + 2 * ‖p.2 - q.1‖) * t) := by
        gcongr
    _ = t * ‖q.2‖ + 2 * ‖p.2 - q.1‖ := by field_simp
    _ < ε := by linarith

theorem mem_of_tendsto_generator {f g : E}
    (h : Tendsto (fun t : ℝ => t⁻¹ • (G.sg t f - f)) (𝓝[>] 0) (𝓝 g)) : (f, g) ∈ G.A := by
  set u := G.res 1 (f - g) with hu
  have hmem : (u, u - (f - g)) ∈ G.A := by
    have := G.res_mem one_pos (f - g); rw [one_smul] at this; exact this
  have hu' := G.tendsto_generator_of_mem hmem
  have hw : Tendsto (fun t : ℝ => t⁻¹ • (G.sg t (f - u) - (f - u))) (𝓝[>] 0) (𝓝 (f - u)) := by
    have := h.sub hu'
    convert this using 1
    · ext t; simp only [map_sub]; rw [← smul_sub]; congr 1; abel
    · show 𝓝 (f - u) = 𝓝 (g - (u - (f - g))); congr 1; abel
  clear_value u
  set w := f - u with hwdef
  clear_value w
  have hw0 : Tendsto (fun t : ℝ => ‖t⁻¹ • (G.sg t w - w) - w‖) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).1 hw
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖w‖ ≤ ‖t⁻¹ • (G.sg t w - w) - w‖ := by
    refine eventually_nhdsWithin_of_forall fun t ht => ?_
    have ht0 : 0 < t := ht
    have e : t⁻¹ • (G.sg t w - w) - w = t⁻¹ • (G.sg t w - (1 + t) • w) := by
      rw [add_smul, one_smul, smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht0.ne',
        one_smul]; abel
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)]
    have h1 : ‖G.sg t w‖ ≤ ‖w‖ := ((G.sg t).le_opNorm _).trans (by
      have := G.norm_sg_le ht0.le
      nlinarith [norm_nonneg w])
    have h2 : (1 + t) * ‖w‖ - ‖G.sg t w‖ ≤ ‖G.sg t w - (1 + t) • w‖ := by
      rw [norm_sub_rev (G.sg t w)]
      have := norm_sub_norm_le ((1 + t) • w) (G.sg t w)
      rwa [norm_smul, Real.norm_of_nonneg (by linarith)] at this
    rw [le_inv_mul_iff₀ ht0]
    nlinarith
  have hw00 : ‖w‖ ≤ 0 := ge_of_tendsto hw0 hle
  have hwz : w = 0 := norm_le_zero_iff.1 hw00
  have hfu : f = u := by rw [hwdef] at hwz; exact sub_eq_zero.1 hwz
  convert hmem using 2
  rw [← hfu]; abel

theorem generator_iff (f g : E) :
    Tendsto (fun t : ℝ => t⁻¹ • (G.sg t f - f)) (𝓝[>] 0) (𝓝 g) ↔ (f, g) ∈ G.A :=
  ⟨G.mem_of_tendsto_generator, fun h => G.tendsto_generator_of_mem (p := (f, g)) h⟩

end HYGen


section Surj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Dense range of `r - G` plus dissipativity of the closed relation `A ⊇ G` gives
surjectivity of `r - A`. -/
theorem surj_of_denseRange (G A : Submodule ℝ (E × E)) (hle : G ≤ A)
    (hA : IsClosed (A : Set (E × E))) {r : ℝ} (hr : 0 < r)
    (hdiss : ∀ p ∈ A, r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖)
    (hrange : Dense ((fun fg : E × E => r • fg.1 - fg.2) '' (G : Set (E × E)))) :
    ∀ h : E, ∃ p ∈ A, r • p.1 - p.2 = h := by
  have : CompleteSpace A := hA.completeSpace_coe
  let L0 : (E × E) →L[ℝ] E := r • ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E
  let L : A →L[ℝ] E := L0.comp A.subtypeL
  have hL : ∀ p : A, L p = r • (p : E × E).1 - (p : E × E).2 := fun p => rfl
  have hbound : ∀ p : A, ‖p‖ ≤ (1 / r + 2) * ‖L p‖ := by
    intro p
    have h1 := hdiss _ p.2
    rw [← hL] at h1
    have h1' : ‖(p : E × E).1‖ ≤ ‖L p‖ / r := by rw [le_div_iff₀ hr]; linarith
    have h2 : ‖(p : E × E).2‖ ≤ 2 * ‖L p‖ := by
      have : (p : E × E).2 = r • (p : E × E).1 - L p := by rw [hL]; abel
      rw [this]
      calc ‖r • (p : E × E).1 - L p‖ ≤ ‖r • (p : E × E).1‖ + ‖L p‖ := norm_sub_le _ _
        _ = r * ‖(p : E × E).1‖ + ‖L p‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
        _ ≤ 2 * ‖L p‖ := by linarith
    have hn : ‖p‖ = max ‖(p : E × E).1‖ ‖(p : E × E).2‖ := by
      rw [Submodule.coe_norm]; rfl
    rw [hn]
    have hLn := norm_nonneg (L p)
    have : ‖L p‖ / r = (1 / r) * ‖L p‖ := by ring
    refine max_le ?_ ?_
    · nlinarith [one_div_pos.2 hr]
    · nlinarith [one_div_pos.2 hr]
  have hanti : AntilipschitzWith (Real.toNNReal (1 / r + 2)) L :=
    L.antilipschitz_of_bound (fun p => by
      rw [Real.coe_toNNReal _ (by positivity)]; exact hbound p)
  have hclosed : IsClosed (Set.range L) := hanti.isClosed_range L.uniformContinuous
  have hrange' : Set.range L = Set.univ := by
    have hd : Dense (Set.range L) := hrange.mono (by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨⟨q, hle hq⟩, rfl⟩)
    rw [← hclosed.closure_eq, hd.closure_eq]
  intro h
  obtain ⟨q, hq⟩ : h ∈ Set.range L := by rw [hrange']; trivial
  exact ⟨q, q.2, hq⟩

/-- One step of the extension of the range condition: from `μ` to any `r ∈ (0, 2μ)`. -/
theorem surj_step (A : Submodule ℝ (E × E))
    (hdiss : ∀ p ∈ A, ∀ r : ℝ, 0 < r → r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖)
    {μ : ℝ} (hμ : 0 < μ) (hsurj : ∀ h : E, ∃ p ∈ A, μ • p.1 - p.2 = h)
    {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * μ) :
    ∀ h : E, ∃ p ∈ A, r • p.1 - p.2 = h := by
  choose P hPA hPe using hsurj
  have hlip : ∀ k k', ‖(P k).1 - (P k').1‖ ≤ (1 / μ) * ‖k - k'‖ := by
    intro k k'
    have := hdiss _ (A.sub_mem (hPA k) (hPA k')) μ hμ
    have e : μ • (P k - P k').1 - (P k - P k').2 = k - k' := by
      simp only [Prod.fst_sub, Prod.snd_sub]
      linear_combination (norm := module) hPe k - hPe k'
    rw [e] at this
    simp only [Prod.fst_sub] at this
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hμ]; linarith
  intro h
  set Φ : E → E := fun u => (P (h + (μ - r) • u)).1
  have hK : |μ - r| / μ < 1 := by
    rw [div_lt_one hμ, abs_lt]; constructor <;> linarith
  have hΦ : ContractingWith (Real.toNNReal (|μ - r| / μ)) Φ := by
    refine ⟨by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by positivity)]; simpa using hK, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
    refine (hlip _ _).trans ?_
    have : h + (μ - r) • u - (h + (μ - r) • v) = (μ - r) • (u - v) := by
      rw [smul_sub]; abel
    rw [this, norm_smul, Real.norm_eq_abs]
    exact le_of_eq (by ring)
  set u := ContractingWith.fixedPoint Φ hΦ
  have hu : Φ u = u := ContractingWith.fixedPoint_isFixedPt hΦ
  refine ⟨P (h + (μ - r) • u), hPA _, ?_⟩
  have e := hPe (h + (μ - r) • u)
  change (P (h + (μ - r) • u)).1 = u at hu
  rw [hu] at e ⊢
  linear_combination (norm := module) e

/-- Surjectivity of `r₀ - A` for one `r₀ > 0` gives surjectivity for all `r > 0`. -/
theorem surj_all_of_surj (A : Submodule ℝ (E × E))
    (hdiss : ∀ p ∈ A, ∀ r : ℝ, 0 < r → r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hsurj : ∀ h : E, ∃ p ∈ A, r₀ • p.1 - p.2 = h) :
    ∀ r : ℝ, 0 < r → ∀ h : E, ∃ p ∈ A, r • p.1 - p.2 = h := by
  have key : ∀ n : ℕ, ∀ r : ℝ, 0 < r → r < 2 ^ n * r₀ →
      ∀ h : E, ∃ p ∈ A, r • p.1 - p.2 = h := by
    intro n
    induction n with
    | zero =>
      intro r hr hrn
      rw [pow_zero, one_mul] at hrn
      exact surj_step A hdiss hr₀ hsurj hr (by linarith)
    | succ n ih =>
      intro r hr hrn
      by_cases hle : r < 2 ^ n * r₀
      · exact ih r hr hle
      · push_neg at hle
        have hpos : 0 < 2 ^ n * r₀ := by positivity
        rw [pow_succ] at hrn
        set μ := (r / 2 + 2 ^ n * r₀) / 2
        have hμ : 0 < μ := by positivity
        have hμn : μ < 2 ^ n * r₀ := by simp only [μ]; linarith
        exact surj_step A hdiss hμ (ih μ hμ hμn) hr (by simp only [μ]; linarith)
  intro r hr
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (r / r₀) (by norm_num : (1 : ℝ) < 2)
  exact key n r hr (by rwa [div_lt_iff₀ hr₀] at hn)

end Surj

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The positive maximum principle gives a lower bound for `r f` in terms of a lower
bound for `r f - g`. -/
theorem pmp_lower_bound (G : Submodule ℝ (C(X, ℝ) × C(X, ℝ)))
    (hpmp : ∀ fg ∈ G, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0)
    {r : ℝ} (hr : 0 < r) {p : C(X, ℝ) × C(X, ℝ)} (hp : p ∈ G) {c : ℝ} (hc : 0 ≤ c)
    (hh : ∀ y, -c ≤ (r • p.1 - p.2) y) (x : X) : -c ≤ r * p.1 x := by
  haveI : Nonempty X := ⟨x⟩
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    p.1.continuous.continuousOn
  have hmin : ∀ y, p.1 x0 ≤ p.1 y := fun y => hx0 (Set.mem_univ y)
  have h1 : r * p.1 x0 ≤ r * p.1 x := by gcongr; exact hmin x
  rcases le_or_gt 0 (p.1 x0) with h | h
  · nlinarith
  · have h2 := hpmp (-p) (G.neg_mem hp) x0 (fun y => by simpa using hmin y) (by simp; linarith)
    simp only [Prod.snd_neg, ContinuousMap.neg_apply, neg_nonpos] at h2
    have h3 := hh x0
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul] at h3
    linarith

/-- The positive maximum principle gives positivity of the resolvent on the closure. -/
theorem nonneg_of_mem_closure_pmp (G : Submodule ℝ (C(X, ℝ) × C(X, ℝ)))
    (hpmp : ∀ fg ∈ G, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0)
    {r : ℝ} (hr : 0 < r) {p : C(X, ℝ) × C(X, ℝ)}
    (hp : p ∈ closure (G : Set (C(X, ℝ) × C(X, ℝ))))
    (hpos : ∀ x, 0 ≤ (r • p.1 - p.2) x) : ∀ x, 0 ≤ p.1 x := by
  intro x
  suffices h : 0 ≤ r * p.1 x from (mul_nonneg_iff_of_pos_left hr).1 h
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / (2 * r + 1)
  have hδ : 0 < δ := by positivity
  obtain ⟨q, hq, hpq⟩ := Metric.mem_closure_iff.1 hp δ hδ
  rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hpq
  have b1 : ∀ y, |p.1 y - q.1 y| ≤ δ := fun y => by
    have := (p.1 - q.1).norm_coe_le_norm y
    simp only [ContinuousMap.sub_apply, Real.norm_eq_abs] at this
    linarith [hpq.1]
  have b2 : ∀ y, |p.2 y - q.2 y| ≤ δ := fun y => by
    have := (p.2 - q.2).norm_coe_le_norm y
    simp only [ContinuousMap.sub_apply, Real.norm_eq_abs] at this
    linarith [hpq.2]
  have hq' := pmp_lower_bound G hpmp hr hq (c := (r + 1) * δ) (by positivity) (fun y => by
    have := hpos y
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul] at this ⊢
    have := b1 y; have := b2 y
    rw [abs_le] at *
    nlinarith) x
  have := b1 x
  rw [abs_le] at this
  have e : ε = (2 * r + 1) * δ := by simp only [δ]; field_simp
  rw [e]; nlinarith

theorem feller_generation_aux (G : Submodule ℝ (C(X, ℝ) × C(X, ℝ)))
    (hpmp : ∀ fg ∈ G, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0)
    (hdense : Dense (Prod.fst '' (G : Set (C(X, ℝ) × C(X, ℝ)))))
    (hrange : ∃ r : ℝ, 0 < r ∧
      Dense ((fun fg : C(X, ℝ) × C(X, ℝ) => r • fg.1 - fg.2) '' (G : Set _)))
    (hone : ((1 : C(X, ℝ)), (0 : C(X, ℝ))) ∈ closure (G : Set (C(X, ℝ) × C(X, ℝ)))) :
    ∃ T : ℝ → C(X, ℝ) →L[ℝ] C(X, ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ closure (G : Set (C(X, ℝ) × C(X, ℝ)))) := by
  obtain ⟨r₀, hr₀, hrg⟩ := hrange
  have hcl : (G.topologicalClosure : Set (C(X, ℝ) × C(X, ℝ))) = closure (G : Set _) :=
    Submodule.topologicalClosure_coe G
  have hdiss : ∀ p ∈ G.topologicalClosure, ∀ r : ℝ, 0 < r → r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖ :=
    fun p hp r _ => dissipative_closure_of_pmp G hpmp r p (by rw [← hcl]; exact hp)
  have hsurj0 := surj_of_denseRange G G.topologicalClosure G.le_topologicalClosure
    G.isClosed_topologicalClosure hr₀ (fun p hp => hdiss p hp r₀ hr₀) hrg
  let H : HYGen C(X, ℝ) :=
    { A := G.topologicalClosure
      closed := G.isClosed_topologicalClosure
      diss := hdiss
      surj := surj_all_of_surj _ hdiss hr₀ hsurj0
      dense := hdense.mono (Set.image_mono (by rw [hcl]; exact subset_closure)) }
  have hres_pos : ∀ r : ℝ, 0 < r → ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ H.res r f x := by
    intro r hr f hf
    have hm : (H.res r f, r • H.res r f - f) ∈ closure (G : Set (C(X, ℝ) × C(X, ℝ))) := by
      rw [← hcl]; exact H.res_mem hr f
    exact nonneg_of_mem_closure_pmp G hpmp hr hm (fun x => by simpa using hf x)
  have hpow_pos : ∀ r : ℝ, 0 < r → ∀ k : ℕ, ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ ((H.res r) ^ k) f x := by
    intro r hr k
    induction k with
    | zero => intro f hf x; simpa using hf x
    | succ k ih =>
      intro f hf x
      rw [pow_succ, ContinuousLinearMap.mul_apply]
      exact ih _ (hres_pos r hr f hf) x
  have hsgn_pos : ∀ n t, 0 ≤ t → ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ H.sgn n t f x := by
    intro n t ht f hf x
    have hs := (H.sgn_hasSum n t f).mapL (ContinuousMap.evalCLM ℝ x)
    refine hs.nonneg fun k => ?_
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (hpow_pos _ (by positivity) k f hf x)
  refine ⟨H.sg, H.isSCCS, ?_, ?_, ?_⟩
  · intro t ht f hf x
    have hlim := ((ContinuousMap.evalCLM ℝ x).continuous.tendsto _).comp (H.tendsto_sg ht f)
    exact ge_of_tendsto' hlim fun n => hsgn_pos n t ht f hf x
  · intro t ht
    have hmem : ((1 : C(X, ℝ)), (0 : C(X, ℝ))) ∈ H.A := by
      show _ ∈ G.topologicalClosure
      rw [← SetLike.mem_coe, hcl]; exact hone
    have h1 : ∀ n, H.sgn n t 1 = 1 := by
      intro n
      have := H.norm_sgn_sub_self n ht 1
      rw [show H.yos n 1 = 0 by simpa using H.yos_apply_of_mem n hmem] at this
      simpa [sub_eq_zero] using this
    have := H.tendsto_sg ht 1
    simp only [h1] at this
    exact (tendsto_nhds_unique this tendsto_const_nhds)
  · intro f g
    rw [H.generator_iff, ← hcl]
    rfl

end EthierKurtz.FellerProof

open EthierKurtz EthierKurtz.FellerProof

theorem solution {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (G : Submodule ℝ (C(X, ℝ) × C(X, ℝ)))
    (hpmp : ∀ fg ∈ G, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0)
    (hdense : Dense (Prod.fst '' (G : Set (C(X, ℝ) × C(X, ℝ)))))
    (hrange : ∃ r : ℝ, 0 < r ∧
      Dense ((fun fg : C(X, ℝ) × C(X, ℝ) => r • fg.1 - fg.2) '' (G : Set _)))
    (hone : ((1 : C(X, ℝ)), (0 : C(X, ℝ))) ∈ closure (G : Set (C(X, ℝ) × C(X, ℝ)))) :
    ∃ T : ℝ → C(X, ℝ) →L[ℝ] C(X, ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ closure (G : Set (C(X, ℝ) × C(X, ℝ)))) :=
  feller_generation_aux G hpmp hdense hrange hone
