-- Prove2me | solution 1 for Dubey1986.Inefficiency.main_theorem_interior
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T00:55:56.898843+00:00
-- url     : https://prove2.me/submissions/33193a51-1312-48dd-8fdb-ec332d98d267

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative
import Theorems.Thm_Dubey1986_Inefficiency_finite_of_transverse
import Theorems.Thm_Dubey1986_Inefficiency_eff_interior_mem_Estar
import Theorems.Thm_Dubey1986_Inefficiency_nash_interior_mem_Nstar

open Dubey1986.Inefficiency Filter Topology Set Manifold

namespace DubeyTransAux

variable {n : ℕ} {k : Fin n → ℕ}

/-- own-block projection -/
noncomputable def piL (k : Fin n → ℕ) : (Fin n → (Strat k →L[ℝ] ℝ)) →L[ℝ] Strat k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A i j => A i (Pi.single i (Pi.single j 1))
      map_add' := by intro A B; funext i j; simp
      map_smul' := by intro c A; funext i j; simp }

lemma piL_apply (A : Fin n → (Strat k →L[ℝ] ℝ)) :
    piL k A = fun i j => A i (Pi.single i (Pi.single j 1)) := rfl

noncomputable def lift (w : Strat k) : Fin n → (Strat k →L[ℝ] ℝ) := fun i =>
  (∑ j, w i j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k i) => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i => Fin (k i) → ℝ) i)

lemma lift_apply (w x : Strat k) (i : Fin n) : lift w i x = ∑ j, w i j * x i j := by
  simp [lift]

lemma piL_lift (w : Strat k) : piL k (lift w) = w := by
  rw [piL_apply]; funext i j
  simp [lift_apply, Pi.single_apply]

lemma piL_eq_zero_iff (A : Fin n → (Strat k →L[ℝ] ℝ)) : piL k A = 0 ↔ A ∈ Nstar k := by
  constructor
  · intro h i v
    let L : (Fin (k i) → ℝ) →L[ℝ] ℝ :=
      (A i).comp (ContinuousLinearMap.single ℝ (fun i => Fin (k i) → ℝ) i)
    have hL : (L : (Fin (k i) → ℝ) →ₗ[ℝ] ℝ) = 0 := by
      apply (Pi.basisFun ℝ (Fin (k i))).ext
      intro j
      have := congrFun (congrFun h i) j
      rw [piL_apply] at this
      simpa [L] using this
    have := congrArg (fun f : (Fin (k i) → ℝ) →ₗ[ℝ] ℝ => f v) hL
    simpa [L] using this
  · intro h
    rw [piL_apply]; funext i j; exact h i _

lemma transverse_iff (D : Strat k →L[ℝ] (Fin n → (Strat k →L[ℝ] ℝ))) :
    LinearMap.range (D : Strat k →ₗ[ℝ] (Fin n → (Strat k →L[ℝ] ℝ))) ⊔ Nstar k = ⊤ ↔
      ((piL k).comp D).det ≠ 0 := by
  rw [ContinuousLinearMap.det, ← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det,
    Module.End.isUnit_iff]
  constructor
  · intro ht
    have hsurj : Function.Surjective (((piL k).comp D : Strat k →L[ℝ] Strat k) :
        Strat k →ₗ[ℝ] Strat k) := by
      intro w
      have hAm : lift w ∈ LinearMap.range (D : Strat k →ₗ[ℝ] _) ⊔ Nstar k := by
        rw [ht]; trivial
      obtain ⟨y, ⟨z, rfl⟩, m, hm, hym⟩ := Submodule.mem_sup.1 hAm
      refine ⟨z, ?_⟩
      have : piL k (lift w) = piL k (D z) + piL k m := by rw [← hym, map_add]; rfl
      rw [(piL_eq_zero_iff m).2 hm, add_zero, piL_lift] at this
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, Function.comp_apply]
      exact this.symm
    exact ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  · rintro ⟨-, hsurj⟩
    rw [eq_top_iff]
    intro A _
    obtain ⟨z, hz⟩ := hsurj (piL k A)
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
      Function.comp_apply] at hz
    have hm : A - D z ∈ Nstar k := by
      rw [← piL_eq_zero_iff, map_sub, hz, sub_self]
    have : A = D z + (A - D z) := by abel
    rw [this]
    exact Submodule.add_mem_sup ⟨z, rfl⟩ hm

/-! C² norm lemmas -/

lemma c2Norm_le {W : Set (Strat k)} {f : Strat k → ℝ} {η : ℝ}
    (h : ∀ y ∈ W, ‖f y‖ ≤ η ∧ ‖fderiv ℝ f y‖ ≤ η ∧ ‖iteratedFDeriv ℝ 2 f y‖ ≤ η) :
    c2Norm W f ≤ ENNReal.ofReal η := by
  unfold c2Norm
  refine iSup₂_le fun y hy => ?_
  obtain ⟨h1, h2, h3⟩ := h y hy
  refine sup_le (sup_le ?_ ?_) ?_ <;> rw [← ofReal_norm] <;>
    exact ENNReal.ofReal_le_ofReal ‹_›

lemma le_c2Norm {W : Set (Strat k)} {f : Strat k → ℝ} {y : Strat k} (hy : y ∈ W) :
    ‖f y‖ₑ ⊔ ‖fderiv ℝ f y‖ₑ ⊔ ‖iteratedFDeriv ℝ 2 f y‖ₑ ≤ c2Norm W f :=
  le_iSup₂ (f := fun s (_ : s ∈ W) => ‖f s‖ₑ ⊔ ‖fderiv ℝ f s‖ₑ ⊔ ‖iteratedFDeriv ℝ 2 f s‖ₑ) y hy

lemma c2Norm_add_le {W : Set (Strat k)} (hW : IsOpen W) {f g : Strat k → ℝ}
    (hf : ContDiffOn ℝ 2 f W) (hg : ContDiffOn ℝ 2 g W) :
    c2Norm W (f + g) ≤ c2Norm W f + c2Norm W g := by
  unfold c2Norm
  refine iSup₂_le fun y hy => ?_
  have hfa : ContDiffAt ℝ 2 f y := hf.contDiffAt (hW.mem_nhds hy)
  have hga : ContDiffAt ℝ 2 g y := hg.contDiffAt (hW.mem_nhds hy)
  have hF := le_c2Norm (f := f) hy
  have hG := le_c2Norm (f := g) hy
  unfold c2Norm at hF hG
  rw [fderiv_add (hfa.differentiableAt (by norm_num)) (hga.differentiableAt (by norm_num)),
    iteratedFDeriv_add_apply (i := 2) hfa hga, Pi.add_apply]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine (enorm_add_le (f y) (g y)).trans (add_le_add ?_ ?_)
    · exact le_trans (le_trans le_sup_left le_sup_left) hF
    · exact le_trans (le_trans le_sup_left le_sup_left) hG
  · refine (enorm_add_le (fderiv ℝ f y) (fderiv ℝ g y)).trans (add_le_add ?_ ?_)
    · exact le_trans (le_trans le_sup_right le_sup_left) hF
    · exact le_trans (le_trans le_sup_right le_sup_left) hG
  · refine (enorm_add_le (iteratedFDeriv ℝ 2 f y) (iteratedFDeriv ℝ 2 g y)).trans (add_le_add ?_ ?_)
    · exact le_trans le_sup_right hF
    · exact le_trans le_sup_right hG

lemma norm_fderiv_fderiv (f : Strat k → ℝ) (y : Strat k) :
    ‖fderiv ℝ (fderiv ℝ f) y‖ = ‖iteratedFDeriv ℝ 2 f y‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

/-- Closeness in C² norm gives closeness of first and second derivatives. -/
lemma c2_close {W : Set (Strat k)} (hW : IsOpen W) {f g : Strat k → ℝ}
    (hf : ContDiffOn ℝ 2 f W) (hg : ContDiffOn ℝ 2 g W) {ε : ℝ}
    (h : c2Norm W (f - g) < ENNReal.ofReal ε) {y : Strat k} (hy : y ∈ W) :
    ‖fderiv ℝ f y - fderiv ℝ g y‖ < ε ∧
      ‖fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ g) y‖ < ε := by
  have hfa : ContDiffAt ℝ 2 f y := hf.contDiffAt (hW.mem_nhds hy)
  have hga : ContDiffAt ℝ 2 g y := hg.contDiffAt (hW.mem_nhds hy)
  have hle := (le_c2Norm (f := f - g) hy).trans_lt h
  have hε : 0 < ε := by
    by_contra hε; rw [not_lt] at hε
    rw [ENNReal.ofReal_of_nonpos hε] at hle; exact absurd hle (by simp)
  have h1 : ‖fderiv ℝ (f - g) y‖ < ε := by
    have := (le_trans le_sup_right le_sup_left).trans_lt hle
    rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hε] at this
    exact this
  have h2 : ‖iteratedFDeriv ℝ 2 (f - g) y‖ < ε := by
    have := (le_sup_right).trans_lt hle
    rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hε] at this
    exact this
  refine ⟨?_, ?_⟩
  · rwa [fderiv_sub (hfa.differentiableAt (by norm_num)) (hga.differentiableAt (by norm_num))] at h1
  · rw [← norm_fderiv_fderiv] at h2
    have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) W := hf.fderiv_of_isOpen hW (by norm_num)
    have hg1 : ContDiffOn ℝ 1 (fderiv ℝ g) W := hg.fderiv_of_isOpen hW (by norm_num)
    have heq : fderiv ℝ (f - g) =ᶠ[𝓝 y] fderiv ℝ f - fderiv ℝ g := by
      filter_upwards [hW.mem_nhds hy] with z hz
      have hfz : ContDiffAt ℝ 2 f z := hf.contDiffAt (hW.mem_nhds hz)
      have hgz : ContDiffAt ℝ 2 g z := hg.contDiffAt (hW.mem_nhds hz)
      exact fderiv_sub (hfz.differentiableAt (by norm_num)) (hgz.differentiableAt (by norm_num))
    rw [heq.fderiv_eq, fderiv_sub
      ((hf1.differentiableOn one_ne_zero).differentiableAt (hW.mem_nhds hy))
      ((hg1.differentiableOn one_ne_zero).differentiableAt (hW.mem_nhds hy))] at h2
    exact h2


lemma trans_iff' (f : Strat k → (Fin n → (Strat k →L[ℝ] ℝ))) (x : Strat k) :
    TransverseAt f (Nstar k) x ↔ piL k (f x) ≠ 0 ∨ ((piL k).comp (fderiv ℝ f x)).det ≠ 0 := by
  unfold TransverseAt
  simp only [transverse_iff, ← piL_eq_zero_iff, Ne]

variable {V : ∀ i, Set (Fin (k i) → ℝ)}

lemma vopen (hVo : ∀ i, IsOpen (V i)) : IsOpen (Vset V) :=
  isOpen_set_pi Set.finite_univ (fun i _ => hVo i)

lemma dmap_C1 (hVo : ∀ i, IsOpen (V i)) {u : Fin n → Strat k → ℝ} (hu : IsGame V u) :
    ContDiffOn ℝ 1 (Dmap u) (Vset V) :=
  contDiffOn_pi.2 fun i => (hu i).1.fderiv_of_isOpen (vopen hVo) (by norm_num)

lemma dmap_diff (hVo : ∀ i, IsOpen (V i)) {u : Fin n → Strat k → ℝ} (hu : IsGame V u)
    {y : Strat k} (hy : y ∈ Vset V) : DifferentiableAt ℝ (Dmap u) y :=
  ((dmap_C1 hVo hu).differentiableOn one_ne_zero).differentiableAt ((vopen hVo).mem_nhds hy)

lemma fderiv_dmap (hVo : ∀ i, IsOpen (V i)) {u : Fin n → Strat k → ℝ} (hu : IsGame V u)
    {y : Strat k} (hy : y ∈ Vset V) :
    fderiv ℝ (Dmap u) y = ContinuousLinearMap.pi fun i => fderiv ℝ (fderiv ℝ (u i)) y := by
  have h1 : ∀ i, DifferentiableAt ℝ (fun z => fderiv ℝ (u i) z) y := fun i =>
    (((hu i).1.fderiv_of_isOpen (vopen hVo) (m := 1) (by norm_num)).differentiableOn
      one_ne_zero).differentiableAt ((vopen hVo).mem_nhds hy)
  exact fderiv_pi h1

lemma dmap_close (hVo : ∀ i, IsOpen (V i)) {u v : Fin n → Strat k → ℝ} (hu : IsGame V u)
    (hv : IsGame V v) {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ i, c2Norm (Vset V) (v i - u i) < ENNReal.ofReal ε) {y : Strat k} (hy : y ∈ Vset V) :
    ‖Dmap v y - Dmap u y‖ ≤ ε ∧ ‖fderiv ℝ (Dmap v) y - fderiv ℝ (Dmap u) y‖ ≤ ε := by
  have hcl := fun i => c2_close (vopen hVo) (hv i).1 (hu i).1 (hc i) hy
  refine ⟨?_, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg hε.le).2 fun i => ?_
    exact (hcl i).1.le
  · rw [fderiv_dmap hVo hu hy, fderiv_dmap hVo hv hy]
    refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun z => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have h := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (fderiv ℝ (v i)) y - fderiv ℝ (fderiv ℝ (u i)) y) z
    simp only [ContinuousLinearMap.sub_apply] at h
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.pi_apply, Pi.sub_apply]
    exact h.trans (mul_le_mul_of_nonneg_right (hcl i).2.le (norm_nonneg _))

lemma open_part (hVo : ∀ i, IsOpen (V i)) {W : ∀ i, Set (Fin (k i) → ℝ)}
    (hWc : ∀ i, IsCompact (W i)) (hWV : ∀ i, W i ⊆ V i)
    {u : Fin n → Strat k → ℝ} (hu : IsGame V u)
    (htr : ∀ x ∈ Set.univ.pi W, TransverseAt (Dmap u) (Nstar k) x) :
    ∃ ε > 0, ∀ v, IsGame V v → (∀ i, c2Norm (Vset V) (v i - u i) < ENNReal.ofReal ε) →
      ∀ x ∈ Set.univ.pi W, TransverseAt (Dmap v) (Nstar k) x := by
  have hWsubV : Set.univ.pi W ⊆ Vset V := fun x hx =>
    Set.mem_univ_pi.2 fun i => hWV i (Set.mem_univ_pi.1 hx i)
  by_contra H
  simp only [not_exists, not_and, not_forall] at H
  have H' : ∀ m : ℕ, ∃ v, IsGame V v ∧ (∀ i, c2Norm (Vset V) (v i - u i) <
      ENNReal.ofReal (1 / ((m:ℝ) + 1))) ∧ ∃ x ∈ Set.univ.pi W,
      piL k (Dmap v x) = 0 ∧ ((piL k).comp (fderiv ℝ (Dmap v) x)).det = 0 := by
    intro m
    obtain ⟨v, hv, hc, x, hx, hnt⟩ := H (1 / ((m:ℝ) + 1)) (by positivity)
    rw [trans_iff'] at hnt
    push Not at hnt
    exact ⟨v, hv, hc, x, hx, hnt⟩
  choose v hv hc x hxW hx0 hdet using H'
  obtain ⟨x0, hx0W, φ, hφ, hlim⟩ := (isCompact_univ_pi hWc).tendsto_subseq hxW
  have hx0V := hWsubV hx0W
  have hbd : ∀ m, ‖Dmap (v m) (x m) - Dmap u (x m)‖ ≤ 1 / ((m:ℝ) + 1) ∧
      ‖fderiv ℝ (Dmap (v m)) (x m) - fderiv ℝ (Dmap u) (x m)‖ ≤ 1 / ((m:ℝ) + 1) :=
    fun m => dmap_close hVo hu (hv m) (by positivity) (hc m) (hWsubV (hxW m))
  have hseq0 : Tendsto (fun m => 1 / ((φ m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  -- limit of `G_u`
  have hG1 : Tendsto (fun m => piL k (Dmap u (x (φ m)))) atTop (𝓝 (piL k (Dmap u x0))) :=
    ((piL k).continuous.tendsto _).comp
      ((dmap_diff hVo hu hx0V).continuousAt.tendsto.comp hlim)
  have hG2 : Tendsto (fun m => piL k (Dmap u (x (φ m)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun m => ?_) (hseq0.const_mul ‖piL k‖ |>.trans (by simp))
    have : piL k (Dmap u (x (φ m))) = - piL k (Dmap (v (φ m)) (x (φ m)) - Dmap u (x (φ m))) := by
      rw [map_sub, hx0 (φ m)]; simp
    rw [this, norm_neg]
    exact ((piL k).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hbd (φ m)).1 (norm_nonneg _))
  have hGx0 : piL k (Dmap u x0) = 0 := tendsto_nhds_unique hG1 hG2
  -- limit of the derivatives
  have hcontD : ContinuousAt (fun y => fderiv ℝ (Dmap u) y) x0 :=
    ((dmap_C1 hVo hu).continuousOn_fderiv_of_isOpen (vopen hVo) le_rfl).continuousAt
      ((vopen hVo).mem_nhds hx0V)
  have hT1 : Tendsto (fun m => (piL k).comp (fderiv ℝ (Dmap u) (x (φ m)))) atTop
      (𝓝 ((piL k).comp (fderiv ℝ (Dmap u) x0))) :=
    (((ContinuousLinearMap.compL ℝ _ _ _) (piL k)).continuous.tendsto _).comp
      (hcontD.tendsto.comp hlim)
  have hT2 : Tendsto (fun m => (piL k).comp (fderiv ℝ (Dmap (v (φ m))) (x (φ m))) -
      (piL k).comp (fderiv ℝ (Dmap u) (x (φ m)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun m => ?_) (hseq0.const_mul ‖piL k‖ |>.trans (by simp))
    rw [← ContinuousLinearMap.comp_sub]
    exact ((piL k).opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hbd (φ m)).2 (norm_nonneg _))
  have hT3 : Tendsto (fun m => (piL k).comp (fderiv ℝ (Dmap (v (φ m))) (x (φ m)))) atTop
      (𝓝 ((piL k).comp (fderiv ℝ (Dmap u) x0))) := by
    have := hT2.add hT1
    simp only [sub_add_cancel, zero_add] at this
    exact this
  have hdet1 := (ContinuousLinearMap.continuous_det.tendsto _).comp hT3
  have hdet0 : ((piL k).comp (fderiv ℝ (Dmap u) x0)).det = 0 := by
    refine tendsto_nhds_unique hdet1 ?_
    simp only [Function.comp_def, hdet (φ _)]
    exact tendsto_const_nhds
  rcases (trans_iff' (Dmap u) x0).1 (htr x0 hx0W) with h | h
  · exact h hGx0
  · exact h hdet0


lemma dense_part (hVo : ∀ i, IsOpen (V i)) {W : ∀ i, Set (Fin (k i) → ℝ)}
    (hWc : ∀ i, IsCompact (W i)) (hWV : ∀ i, W i ⊆ V i)
    {u : Fin n → Strat k → ℝ} (hu : IsGame V u) {ε : ℝ} (hε : 0 < ε) :
    ∃ v, IsGame V v ∧ (∀ x ∈ Set.univ.pi W, TransverseAt (Dmap v) (Nstar k) x) ∧
      ∀ i, c2Norm (Vset V) (v i - u i) < ENNReal.ofReal ε := by
  set K := Set.univ.pi W with hK
  have hKc : IsCompact K := isCompact_univ_pi hWc
  have hKV : K ⊆ Vset V := fun x hx =>
    Set.mem_univ_pi.2 fun i => hWV i (Set.mem_univ_pi.1 hx i)
  -- Step 1: a smooth cutoff, equal to `1` near `K`, with compact support.
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, Strat k)
    (n := 2) (Metric.isOpen_thickening (δ := 1) (E := K)).isClosed_compl hKc.isClosed
    (disjoint_compl_left_iff_subset.2 (Metric.self_subset_thickening one_pos K))
  set ψ : Strat k → ℝ := fun y => f y with hψdef
  have hψ : ContDiff ℝ 2 ψ := contMDiff_iff_contDiff.1 f.contMDiff
  have hψ1 : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, ψ y = 1 := fun x hx =>
    (eventually_nhdsSet_iff_forall.1 hf1) x hx
  have hψs : HasCompactSupport ψ :=
    HasCompactSupport.intro (hKc.cthickening (r := 1)) fun x hx =>
      hf0.self_of_nhdsSet x fun h => hx (Metric.thickening_subset_cthickening _ _ h)
  -- Step 2: the bump-localised coordinate functions and uniform bounds.
  let g : ∀ i, Fin (k i) → Strat k → ℝ := fun i j y => ψ y * y i j
  have hg : ∀ i j, ContDiff ℝ 2 (g i j) := fun i j => hψ.mul
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k i) => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i => Fin (k i) → ℝ) i)).contDiff
  have hgs : ∀ i j, HasCompactSupport (g i j) := fun i j => hψs.mul_right
  have hCex : ∀ i j (m : Fin 3), ∃ C, ∀ y, ‖iteratedFDeriv ℝ m (g i j) y‖ ≤ C := by
    intro i j m
    have hm : ((m : ℕ) : WithTop ℕ∞) ≤ 2 := by
      have := m.isLt; norm_cast; omega
    exact (ContDiff.continuous_iteratedFDeriv hm (hg i j)).bounded_above_of_compact_support
      ((hgs i j).iteratedFDeriv m)
  choose C hC using hCex
  set B : ℝ := ∑ i, ∑ j, ∑ m : Fin 3, |C i j m| with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hB : ∀ i j (m : Fin 3) y, ‖iteratedFDeriv ℝ m (g i j) y‖ ≤ B := by
    intro i j m y
    refine (hC i j m y).trans ((le_abs_self _).trans ?_)
    have h1 : |C i j m| ≤ ∑ m' : Fin 3, |C i j m'| :=
      Finset.single_le_sum (f := fun m' => |C i j m'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ m)
    have h2 : ∑ m' : Fin 3, |C i j m'| ≤ ∑ j', ∑ m' : Fin 3, |C i j' m'| :=
      Finset.single_le_sum (f := fun j' => ∑ m' : Fin 3, |C i j' m'|)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    have h3 : ∑ j', ∑ m' : Fin 3, |C i j' m'| ≤ B :=
      Finset.single_le_sum (f := fun i' => ∑ j', ∑ m' : Fin 3, |C i' j' m'|)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    linarith
  -- Step 3: Sard: the critical values of `G_u` form a null set.
  let Gu : Strat k → Strat k := fun y => piL k (Dmap u y)
  let Cr : Set (Strat k) :=
    {y | y ∈ Vset V ∧ ((piL k).comp (fderiv ℝ (Dmap u) y)).det = 0}
  let μ : MeasureTheory.Measure (Strat k) := MeasureTheory.Measure.addHaar
  have hμ : μ (Gu '' Cr) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun y hy => ((piL k).hasFDerivAt.comp y (dmap_diff hVo hu hy.1).hasFDerivAt).hasFDerivWithinAt)
      (fun y hy => hy.2)
  set R : ℝ := ∑ i, (k i : ℝ) with hRdef
  have hR0 : 0 ≤ R := by positivity
  set δ : ℝ := ε / (2 * ((R + 1) * (B + 1))) with hδdef
  have hδ : 0 < δ := by positivity
  have hnsub : ¬ (Metric.ball (0 : Strat k) δ ⊆ Gu '' Cr) := fun h =>
    (Metric.measure_ball_pos μ 0 hδ).ne' (MeasureTheory.measure_mono_null h hμ)
  obtain ⟨b, hb, hbn⟩ := Set.not_subset.1 hnsub
  have hbδ : ‖b‖ < δ := by simpa using hb
  -- Step 4: the perturbation.
  set a : Strat k := -b with hadef
  have ha : ‖a‖ < δ := by rw [hadef, norm_neg]; exact hbδ
  let P : Fin n → Strat k → ℝ := fun i y => ∑ j, a i j * g i j y
  have hP : ∀ i, ContDiff ℝ 2 (P i) := fun i =>
    ContDiff.sum fun j _ => contDiff_const.mul (hg i j)
  have hPb : ∀ i y (m : Fin 3), ‖iteratedFDeriv ℝ m (P i) y‖ ≤ R * ‖a‖ * B := by
    intro i y m
    have hm : ((m : ℕ) : WithTop ℕ∞) ≤ 2 := by
      have := m.isLt; norm_cast; omega
    have hcd : ∀ j ∈ (Finset.univ : Finset (Fin (k i))),
        ContDiffAt ℝ m (fun y => a i j • g i j y) y := fun j _ =>
      ((hg i j).const_smul (a i j)).contDiffAt.of_le hm
    have hPe : P i = fun y => ∑ j, a i j • g i j y := rfl
    rw [hPe, iteratedFDeriv_fun_sum_apply hcd]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j, ‖iteratedFDeriv ℝ m (fun y => a i j • g i j y) y‖ ≤ ‖a‖ * B := by
      intro j
      rw [iteratedFDeriv_const_smul_apply' ((hg i j).contDiffAt.of_le hm), norm_smul]
      have h1 : ‖a i j‖ ≤ ‖a‖ := (norm_le_pi_norm (a i) j).trans (norm_le_pi_norm a i)
      exact mul_le_mul h1 (hB i j m y) (norm_nonneg _) (norm_nonneg _)
    refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hkR : (k i : ℝ) ≤ R :=
      Finset.single_le_sum (f := fun i' => (k i' : ℝ)) (fun _ _ => by positivity)
        (Finset.mem_univ i)
    have := mul_nonneg (norm_nonneg a) hB0
    nlinarith
  have hηε : R * ‖a‖ * B < ε := by
    have h1 : R * ‖a‖ * B ≤ (R + 1) * (B + 1) * ‖a‖ := by
      have := norm_nonneg a
      nlinarith [mul_nonneg hR0 hB0, mul_nonneg this hB0, mul_nonneg this hR0]
    have h2 : (R + 1) * (B + 1) * ‖a‖ ≤ (R + 1) * (B + 1) * δ :=
      mul_le_mul_of_nonneg_left ha.le (by positivity)
    have h3 : (R + 1) * (B + 1) * δ = ε / 2 := by
      rw [hδdef]; field_simp
    linarith
  have hPc : ∀ i, c2Norm (Vset V) (P i) < ENNReal.ofReal ε := by
    intro i
    refine lt_of_le_of_lt (c2Norm_le (η := R * ‖a‖ * B) fun y _ => ⟨?_, ?_, ?_⟩)
      ((ENNReal.ofReal_lt_ofReal_iff hε).2 hηε)
    · have := hPb i y 0; rwa [Fin.val_zero, norm_iteratedFDeriv_zero] at this
    · have := hPb i y 1; rwa [Fin.val_one, norm_iteratedFDeriv_one] at this
    · exact hPb i y 2
  let v : Fin n → Strat k → ℝ := fun i y => u i y + P i y
  have hvu : ∀ i, v i - u i = P i := fun i => by funext y; simp [v]
  have hvg : IsGame V v := by
    intro i
    refine ⟨(hu i).1.add (hP i).contDiffOn, ?_⟩
    have := c2Norm_add_le (vopen hVo) (hu i).1 (hP i).contDiffOn
    refine lt_of_le_of_lt this (ENNReal.add_lt_top.2 ⟨(hu i).2, (hPc i).trans ENNReal.ofReal_lt_top⟩)
  refine ⟨v, hvg, ?_, fun i => by rw [hvu]; exact hPc i⟩
  -- Step 5: transversality of the perturbed game on `K`.
  intro x hx
  have hxV := hKV hx
  have hloc : ∀ᶠ y in 𝓝 x, ψ y = 1 ∧ y ∈ Vset V :=
    (hψ1 x hx).and ((vopen hVo).mem_nhds hxV)
  have hDv : ∀ᶠ y in 𝓝 x, Dmap v y = Dmap u y + lift a := by
    filter_upwards [hloc.eventually_nhds] with y hy
    have hyV := hy.self_of_nhds.2
    funext i
    have hPe : P i =ᶠ[𝓝 y] ⇑(lift a i) := by
      filter_upwards [hy] with z hz
      simp [P, g, hz.1, lift_apply]
    have hud : DifferentiableAt ℝ (u i) y :=
      ((hu i).1.contDiffAt ((vopen hVo).mem_nhds hyV)).differentiableAt (by norm_num)
    have hPd : DifferentiableAt ℝ (P i) y := (hP i).differentiable (by norm_num) y
    show fderiv ℝ (fun y => u i y + P i y) y = fderiv ℝ (u i) y + lift a i
    rw [fderiv_fun_add hud hPd, hPe.fderiv_eq, ContinuousLinearMap.fderiv]
  have hDvx : Dmap v x = Dmap u x + lift a := hDv.self_of_nhds
  have hDv' : Dmap v =ᶠ[𝓝 x] fun y => Dmap u y + lift a := hDv
  have hDDvx : fderiv ℝ (Dmap v) x = fderiv ℝ (Dmap u) x := by
    rw [hDv'.fderiv_eq, fderiv_add_const]
  rw [trans_iff', hDvx, hDDvx]
  by_cases h0 : piL k (Dmap u x + lift a) = 0
  · right
    intro hdet
    apply hbn
    refine ⟨x, ⟨hxV, hdet⟩, ?_⟩
    rw [map_add, piL_lift, hadef] at h0
    show piL k (Dmap u x) = b
    have := congrArg (· + b) h0
    simpa using this
  · left; exact h0


/-! ## Additional lemmas for the interior theorem -/

lemma simplex_compact (m : ℕ) : IsCompact (simplex m) := by
  have hcl : IsClosed (simplex m) := by
    have : simplex m = (⋂ j, {x : Fin m → ℝ | 0 ≤ x j}) ∩ {x | ∑ j, x j ≤ 1} := by
      ext x; simp [simplex]
    rw [this]
    exact IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j))
      (isClosed_le (by fun_prop) continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin m → ℝ)) (r := 1)).subset ?_
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 j)]
  exact (Finset.single_le_sum (f := x) (fun j _ => hx.1 j) (Finset.mem_univ j)).trans hx.2

lemma rot_ne (n : ℕ) (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h1 : (1 : Fin (m + 2)) = 0 := by
    have := congrArg (· - i) h; simpa using this
  exact absurd h1 (by simp [Fin.ext_iff])

/-- A fixed matrix in `N*` with linearly independent rows. -/
noncomputable def C0 (hk : ∀ i, 1 ≤ k i) : Fin n → (Strat k →L[ℝ] ℝ) := fun i =>
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k (finRotate n i)) => ℝ)
      ⟨0, hk (finRotate n i)⟩).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun i => Fin (k i) → ℝ) (finRotate n i))

lemma C0_apply (hk : ∀ i, 1 ≤ k i) (i : Fin n) (y : Strat k) :
    C0 hk i y = y (finRotate n i) ⟨0, hk (finRotate n i)⟩ := rfl

lemma C0_mem (hn : 2 ≤ n) (hk : ∀ i, 1 ≤ k i) : C0 hk ∈ Nstar k := by
  intro i v
  rw [C0_apply, Pi.single_eq_of_ne (rot_ne n hn i)]
  rfl

lemma bad_finite (hk : ∀ i, 1 ≤ k i) (M : Fin n → (Strat k →L[ℝ] ℝ)) :
    {t : ℝ | ¬ LinearIndependent ℝ (M + t • C0 hk)}.Finite := by
  let σ := finRotate n
  let e : Fin n → Strat k := fun l' => Pi.single (σ l') (Pi.single (⟨0, hk (σ l')⟩ : Fin (k (σ l'))) 1)
  let ev : (Fin n → (Strat k →L[ℝ] ℝ)) → Matrix (Fin n) (Fin n) ℝ := fun A l l' => A l (e l')
  have hev_li : ∀ A, (ev A).det ≠ 0 → LinearIndependent ℝ A := by
    intro A hA
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hv : Matrix.vecMul c (ev A) = 0 := by
      funext l'
      have := congrArg (fun F : Strat k →L[ℝ] ℝ => F (e l')) hc
      simpa [Matrix.vecMul, dotProduct, ev] using this
    have := Matrix.eq_zero_of_vecMul_eq_zero hA hv
    exact fun i => congrFun this i
  have hevC : ev (C0 hk) = 1 := by
    funext l l'
    show C0 hk l (e l') = (1 : Matrix (Fin n) (Fin n) ℝ) l l'
    rw [C0_apply]
    by_cases h : l = l'
    · subst h; simp [e, σ]
    · have hs : σ l ≠ σ l' := fun h' => h (σ.injective h')
      simp only [e]
      rw [Pi.single_eq_of_ne hs, Matrix.one_apply_ne h]
      rfl
  have hevlin : ∀ t : ℝ, ev (M + t • C0 hk) = ev M + t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    intro t; rw [← hevC]; funext l l'; simp [ev]; rfl
  have hne : (Matrix.charpoly (-ev M)) ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  by_contra hroot
  apply ht
  apply hev_li
  rw [hevlin]
  have := Matrix.eval_charpoly (-ev M) t
  rw [Polynomial.IsRoot.def] at hroot
  intro h0
  apply hroot
  rw [this]
  convert h0 using 2
  rw [sub_neg_eq_add, add_comm, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

lemma open_indep (hVo : ∀ i, IsOpen (V i)) (hSV : ∀ i, simplex (k i) ⊆ V i)
    {u : Fin n → Strat k → ℝ} (hu : IsGame V u)
    (hind : ∀ x ∈ S k, piL k (Dmap u x) = 0 → LinearIndependent ℝ (Dmap u x)) :
    ∃ ε > 0, ∀ v, IsGame V v → (∀ i, c2Norm (Vset V) (v i - u i) < ENNReal.ofReal ε) →
      ∀ x ∈ S k, piL k (Dmap v x) = 0 → LinearIndependent ℝ (Dmap v x) := by
  have hSsubV : S k ⊆ Vset V := fun x hx =>
    Set.mem_univ_pi.2 fun i => hSV i (Set.mem_univ_pi.1 hx i)
  have hSc : IsCompact (S k) := isCompact_univ_pi fun i => simplex_compact (k i)
  by_contra H
  simp only [not_exists, not_and, not_forall] at H
  have H' : ∀ m : ℕ, ∃ v, IsGame V v ∧ (∀ i, c2Norm (Vset V) (v i - u i) <
      ENNReal.ofReal (1 / ((m:ℝ) + 1))) ∧ ∃ x ∈ S k,
      piL k (Dmap v x) = 0 ∧ ¬ LinearIndependent ℝ (Dmap v x) := by
    intro m
    obtain ⟨v, hv, hc, x, hx, h0, hli⟩ := H (1 / ((m:ℝ) + 1)) (by positivity)
    exact ⟨v, hv, hc, x, hx, h0, hli⟩
  choose v hv hc x hxS hx0 hdep using H'
  obtain ⟨x0, hx0S, φ, hφ, hlim⟩ := hSc.tendsto_subseq hxS
  have hx0V := hSsubV hx0S
  have hbd : ∀ m, ‖Dmap (v m) (x m) - Dmap u (x m)‖ ≤ 1 / ((m:ℝ) + 1) :=
    fun m => (dmap_close hVo hu (hv m) (by positivity) (hc m) (hSsubV (hxS m))).1
  have hseq0 : Tendsto (fun m => 1 / ((φ m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hD1 : Tendsto (fun m => Dmap u (x (φ m))) atTop (𝓝 (Dmap u x0)) :=
    (dmap_diff hVo hu hx0V).continuousAt.tendsto.comp hlim
  have hD2 : Tendsto (fun m => Dmap (v (φ m)) (x (φ m)) - Dmap u (x (φ m))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun m => hbd (φ m)) hseq0
  have hD3 : Tendsto (fun m => Dmap (v (φ m)) (x (φ m))) atTop (𝓝 (Dmap u x0)) := by
    have := hD2.add hD1
    simp only [sub_add_cancel, zero_add] at this
    exact this
  have hG1 : Tendsto (fun m => piL k (Dmap (v (φ m)) (x (φ m)))) atTop (𝓝 (piL k (Dmap u x0))) :=
    ((piL k).continuous.tendsto _).comp hD3
  have hGx0 : piL k (Dmap u x0) = 0 := by
    refine tendsto_nhds_unique hG1 ?_
    simp only [hx0 (φ _)]
    exact tendsto_const_nhds
  have hclosed : IsClosed {A : Fin n → (Strat k →L[ℝ] ℝ) | ¬ LinearIndependent ℝ A} :=
    isOpen_setOfPred_linearIndependent.isClosed_compl
  have hdep0 : ¬ LinearIndependent ℝ (Dmap u x0) :=
    hclosed.mem_of_tendsto hD3 (Eventually.of_forall fun m => hdep (φ m))
  exact hdep0 (hind x0 hx0S hGx0)

lemma perturb_line (hVo : ∀ i, IsOpen (V i)) {K : Set (Strat k)} (hKc : IsCompact K)
    (L : Fin n → (Strat k →L[ℝ] ℝ)) :
    ∃ B ≥ 0, ∀ u, IsGame V u → ∀ t : ℝ, ∃ v, IsGame V v ∧
      (∀ i, c2Norm (Vset V) (v i - u i) ≤ ENNReal.ofReal (|t| * B)) ∧
      ∀ x ∈ K, ∀ᶠ y in 𝓝 x, ∀ i, v i =ᶠ[𝓝 y] fun z => u i z + t * L i z := by
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, Strat k)
    (n := 2) (Metric.isOpen_thickening (δ := 1) (E := K)).isClosed_compl hKc.isClosed
    (disjoint_compl_left_iff_subset.2 (Metric.self_subset_thickening one_pos K))
  set ψ : Strat k → ℝ := fun y => f y with hψdef
  have hψ : ContDiff ℝ 2 ψ := contMDiff_iff_contDiff.1 f.contMDiff
  have hψ1 : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, ψ y = 1 := fun x hx =>
    (eventually_nhdsSet_iff_forall.1 hf1) x hx
  have hψs : HasCompactSupport ψ :=
    HasCompactSupport.intro (hKc.cthickening (r := 1)) fun x hx =>
      hf0.self_of_nhdsSet x fun h => hx (Metric.thickening_subset_cthickening _ _ h)
  let h : Fin n → Strat k → ℝ := fun i y => ψ y * L i y
  have hh : ∀ i, ContDiff ℝ 2 (h i) := fun i => hψ.mul (L i).contDiff
  have hhs : ∀ i, HasCompactSupport (h i) := fun i => hψs.mul_right
  have hCex : ∀ i (m : Fin 3), ∃ C, ∀ y, ‖iteratedFDeriv ℝ m (h i) y‖ ≤ C := by
    intro i m
    have hm : ((m : ℕ) : WithTop ℕ∞) ≤ 2 := by
      have := m.isLt; norm_cast; omega
    exact (ContDiff.continuous_iteratedFDeriv hm (hh i)).bounded_above_of_compact_support
      ((hhs i).iteratedFDeriv m)
  choose C hC using hCex
  set B : ℝ := ∑ i, ∑ m : Fin 3, |C i m| with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hB : ∀ i (m : Fin 3) y, ‖iteratedFDeriv ℝ m (h i) y‖ ≤ B := by
    intro i m y
    refine (hC i m y).trans ((le_abs_self _).trans ?_)
    have h1 : |C i m| ≤ ∑ m' : Fin 3, |C i m'| :=
      Finset.single_le_sum (f := fun m' => |C i m'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ m)
    have h2 : ∑ m' : Fin 3, |C i m'| ≤ B :=
      Finset.single_le_sum (f := fun i' => ∑ m' : Fin 3, |C i' m'|)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    linarith
  refine ⟨B, hB0, fun u hu t => ?_⟩
  let P : Fin n → Strat k → ℝ := fun i y => t • h i y
  have hP : ∀ i, ContDiff ℝ 2 (P i) := fun i => (hh i).const_smul t
  have hPb : ∀ i y (m : Fin 3), ‖iteratedFDeriv ℝ m (P i) y‖ ≤ |t| * B := by
    intro i y m
    have hm : ((m : ℕ) : WithTop ℕ∞) ≤ 2 := by
      have := m.isLt; norm_cast; omega
    rw [iteratedFDeriv_const_smul_apply' ((hh i).contDiffAt.of_le hm), norm_smul,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB i m y) (abs_nonneg _)
  have hPc : ∀ i, c2Norm (Vset V) (P i) ≤ ENNReal.ofReal (|t| * B) := by
    intro i
    refine c2Norm_le fun y _ => ⟨?_, ?_, ?_⟩
    · have := hPb i y 0; rwa [Fin.val_zero, norm_iteratedFDeriv_zero] at this
    · have := hPb i y 1; rwa [Fin.val_one, norm_iteratedFDeriv_one] at this
    · exact hPb i y 2
  let v : Fin n → Strat k → ℝ := fun i y => u i y + P i y
  have hvu : ∀ i, v i - u i = P i := fun i => by funext y; simp [v]
  have hvg : IsGame V v := by
    intro i
    refine ⟨(hu i).1.add (hP i).contDiffOn, ?_⟩
    have := c2Norm_add_le (vopen hVo) (hu i).1 (hP i).contDiffOn
    exact lt_of_le_of_lt this (ENNReal.add_lt_top.2 ⟨(hu i).2,
      lt_of_le_of_lt (hPc i) ENNReal.ofReal_lt_top⟩)
  refine ⟨v, hvg, fun i => by rw [hvu]; exact hPc i, ?_⟩
  intro x hx
  filter_upwards [(hψ1 x hx).eventually_nhds] with y hy i
  filter_upwards [hy] with z hz
  simp [v, P, h, hz]

end DubeyTransAux

open DubeyTransAux in
theorem solution {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (hSV : ∀ i, simplex (k i) ⊆ V i) :
    ∃ Ustar : Set (Fin n → Strat k → ℝ), IsOpenDense V Ustar ∧ ∀ u ∈ Ustar,
      {s | s ∈ NashSet u ∧ ∀ i, s i ∈ interior (simplex (k i))}.Finite ∧
      ∀ s ∈ NashSet u ∩ EffSet u, ¬ ∀ i, s i ∈ interior (simplex (k i)) := by
  -- compact neighbourhoods `W^i` of the simplices inside `V^i`
  have hWex : ∀ i, ∃ W : Set (Fin (k i) → ℝ), IsCompact W ∧ simplex (k i) ⊆ interior W ∧
      W ⊆ V i := by
    intro i
    obtain ⟨δ, hδ, hδV⟩ := (simplex_compact (k i)).exists_cthickening_subset_open (hVo i) (hSV i)
    refine ⟨Metric.cthickening δ (simplex (k i)), (simplex_compact (k i)).cthickening, ?_, hδV⟩
    exact (Metric.self_subset_thickening hδ _).trans
      (interior_maximal (Metric.thickening_subset_cthickening _ _) Metric.isOpen_thickening)
  choose W hWc hSW hWV using hWex
  have hSsubW : S k ⊆ Set.univ.pi W := fun x hx =>
    Set.mem_univ_pi.2 fun i => interior_subset (hSW i (Set.mem_univ_pi.1 hx i))
  let Good : (Fin n → Strat k → ℝ) → Prop := fun u =>
    IsGame V u ∧ (∀ x ∈ Set.univ.pi W, TransverseAt (Dmap u) (Nstar k) x) ∧
      ∀ x ∈ S k, piL k (Dmap u x) = 0 → LinearIndependent ℝ (Dmap u x)
  refine ⟨{u | Good u}, ⟨fun u hu => hu.1, ?_, ?_⟩, ?_⟩
  · -- openness
    rintro u ⟨hu, htr, hind⟩
    obtain ⟨ε1, hε1, h1⟩ := open_part hVo hWc hWV hu htr
    obtain ⟨ε2, hε2, h2⟩ := open_indep hVo hSV hu hind
    refine ⟨min ε1 ε2, lt_min hε1 hε2, fun v hv hc => ⟨hv, ?_, ?_⟩⟩
    · exact h1 v hv fun i => (hc i).trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    · exact h2 v hv fun i => (hc i).trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  · -- density
    intro u hu ε hε
    obtain ⟨u1, hu1, htr1, hc1⟩ := dense_part hVo hWc hWV hu (half_pos hε)
    obtain ⟨ε1, hε1, hop1⟩ := open_part hVo hWc hWV hu1 htr1
    have hZfin := (finite_of_transverse hn k hk V hVo hSV W hWc hSW hWV u1 hu1 htr1).1
    set Z := S k ∩ Dmap u1 ⁻¹' (Nstar k : Set (Fin n → (Strat k →L[ℝ] ℝ)))
    obtain ⟨B, hB0, hpert⟩ := perturb_line (V := V) hVo (isCompact_univ_pi hWc) (C0 hk)
    have hbad : (⋃ z ∈ Z, {t : ℝ | ¬ LinearIndependent ℝ (Dmap u1 z + t • C0 hk)}).Finite :=
      hZfin.biUnion fun z _ => bad_finite hk _
    set η := min (ε / 2) ε1 / (B + 1) with hηdef
    have hη : 0 < η := by positivity
    obtain ⟨t, ⟨ht0, htη⟩, htbad⟩ := ((Set.Ioo_infinite hη).sdiff hbad).nonempty
    obtain ⟨v, hv, hcv, hloc⟩ := hpert u1 hu1 t
    have htB : |t| * B < min (ε / 2) ε1 := by
      rw [abs_of_pos ht0]
      have h1 : t * B ≤ t * (B + 1) := by nlinarith
      have h2 : t * (B + 1) < η * (B + 1) := mul_lt_mul_of_pos_right htη (by positivity)
      have h3 : η * (B + 1) = min (ε / 2) ε1 := by rw [hηdef]; field_simp
      linarith
    have hcv' : ∀ i, c2Norm (Vset V) (v i - u1 i) < ENNReal.ofReal (min (ε / 2) ε1) :=
      fun i => (hcv i).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 htB)
    refine ⟨v, ⟨hv, hop1 v hv fun i => (hcv' i).trans_le
      (ENNReal.ofReal_le_ofReal (min_le_right _ _)), ?_⟩, ?_⟩
    · intro x hxS h0
      have hxW := hSsubW hxS
      have hloc' := (hloc x hxW).self_of_nhds
      have hDv : Dmap v x = Dmap u1 x + t • C0 hk := by
        funext i
        have hxV : x ∈ Vset V := Set.mem_univ_pi.2 fun i => hSV i (Set.mem_univ_pi.1 hxS i)
        have hud : DifferentiableAt ℝ (u1 i) x :=
          ((hu1 i).1.contDiffAt ((vopen hVo).mem_nhds hxV)).differentiableAt (by norm_num)
        show fderiv ℝ (v i) x = fderiv ℝ (u1 i) x + t • C0 hk i
        rw [(hloc' i).fderiv_eq, fderiv_fun_add hud
          (((C0 hk i).differentiableAt).const_mul t), fderiv_const_mul
          (C0 hk i).differentiableAt, ContinuousLinearMap.fderiv]
      rw [hDv, map_add, map_smul, (piL_eq_zero_iff _).2 (C0_mem hn hk), smul_zero,
        add_zero] at h0
      have hxZ : x ∈ Z := ⟨hxS, (piL_eq_zero_iff _).1 h0⟩
      rw [hDv]
      by_contra hli
      exact htbad (Set.mem_biUnion hxZ hli)
    · intro i
      have hsplit : v i - u i = (v i - u1 i) + (u1 i - u i) := by abel
      rw [hsplit]
      refine lt_of_le_of_lt (c2Norm_add_le (vopen hVo) ((hv i).1.sub (hu1 i).1)
        ((hu1 i).1.sub (hu i).1)) ?_
      have h1 : c2Norm (Vset V) (v i - u1 i) < ENNReal.ofReal (ε / 2) :=
        (hcv' i).trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
      calc c2Norm (Vset V) (v i - u1 i) + c2Norm (Vset V) (u1 i - u i)
          < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
            ENNReal.add_lt_add h1 (hc1 i)
        _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  · -- the two conclusions
    rintro u ⟨hu, htr, hind⟩
    refine ⟨(finite_of_transverse hn k hk V hVo hSV W hWc hSW hWV u hu htr).2, ?_⟩
    rintro s ⟨hN, hE⟩ hint
    have h1 := nash_interior_mem_Nstar hn k hk V hVo hSV u hu s hint hN
    have h2 := eff_interior_mem_Estar hn k hk V hVo hSV u hu s hint hE
    exact h2 (hind s hN.1 ((piL_eq_zero_iff _).2 h1))
