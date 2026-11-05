-- Prove2me | solution 1 for Dubey1986.Inefficiency.finite_of_transverse
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T00:39:27.699518+00:00
-- url     : https://prove2.me/submissions/d93b13fd-edc1-4840-be77-b3cc6437c0a2

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative
import Theorems.Thm_Dubey1986_Inefficiency_nash_interior_mem_Nstar

open Dubey1986.Inefficiency Filter Topology

theorem solution {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (hSV : ∀ i, simplex (k i) ⊆ V i) (W : ∀ i, Set (Fin (k i) → ℝ))
    (hWc : ∀ i, IsCompact (W i)) (hSW : ∀ i, simplex (k i) ⊆ interior (W i))
    (hWV : ∀ i, W i ⊆ V i) (u : Fin n → Strat k → ℝ) (hu : IsGame V u)
    (htr : ∀ x ∈ Set.univ.pi W, TransverseAt (Dmap u) (Nstar k) x) :
    (S k ∩ Dmap u ⁻¹' (Nstar k : Set (Fin n → (Strat k →L[ℝ] ℝ)))).Finite ∧
    {s | s ∈ NashSet u ∧ ∀ i, s i ∈ interior (simplex (k i))}.Finite := by
  set Z := S k ∩ Dmap u ⁻¹' (Nstar k : Set (Fin n → (Strat k →L[ℝ] ℝ))) with hZ
  have hVopen : IsOpen (Vset V) := isOpen_set_pi Set.finite_univ (fun i _ => hVo i)
  have hSsubW : S k ⊆ Set.univ.pi W := fun x hx =>
    Set.mem_univ_pi.2 fun i => interior_subset (hSW i (Set.mem_univ_pi.1 hx i))
  have hWsubV : Set.univ.pi W ⊆ Vset V := fun x hx =>
    Set.mem_univ_pi.2 fun i => hWV i (Set.mem_univ_pi.1 hx i)
  -- `Dmap u` is differentiable on `V`.
  have hDdiff : ∀ x ∈ Vset V, DifferentiableAt ℝ (Dmap u) x := by
    intro x hx
    apply differentiableAt_pi.2
    intro i
    have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ (u i) y) (Vset V) :=
      (hu i).1.fderiv_of_isOpen hVopen (by norm_num)
    exact (h1.differentiableOn one_ne_zero).differentiableAt (hVopen.mem_nhds hx)
  -- The "own block" projection `π`, with kernel containing `N*`.
  let πl : (Fin n → (Strat k →L[ℝ] ℝ)) →ₗ[ℝ] Strat k :=
    { toFun := fun A i j => A i (Pi.single i (Pi.single j 1))
      map_add' := by intro A B; funext i j; simp
      map_smul' := by intro c A; funext i j; simp }
  let π : (Fin n → (Strat k →L[ℝ] ℝ)) →L[ℝ] Strat k := πl.toContinuousLinearMap
  have hπ : ∀ A, π A = fun i j => A i (Pi.single i (Pi.single j 1)) := fun A => rfl
  have hπN : ∀ A ∈ Nstar k, π A = 0 := by
    intro A hA; rw [hπ]; funext i j; exact hA i _
  have hπsurj : ∀ w : Strat k, ∃ A, π A = w := by
    intro w
    refine ⟨fun i => (∑ j, w i j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k i) => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i => Fin (k i) → ℝ) i), ?_⟩
    rw [hπ]; funext i j
    simp [Pi.single_apply]
  -- Isolation of points of `Z`.
  have hiso : ∀ x ∈ Z, ∀ᶠ y in 𝓝[≠] x, y ∉ Z := by
    intro x hx
    have hxW := hSsubW hx.1
    have hxV := hWsubV hxW
    set D := fderiv ℝ (Dmap u) x
    have hDm : HasFDerivAt (Dmap u) D x := (hDdiff x hxV).hasFDerivAt
    have ht : LinearMap.range (D : Strat k →ₗ[ℝ] (Fin n → (Strat k →L[ℝ] ℝ))) ⊔ Nstar k = ⊤ := by
      rcases htr x hxW with h | h
      · exact absurd hx.2 h
      · exact h
    have hG : HasFDerivAt (fun y => π (Dmap u y)) (π.comp D) x := π.hasFDerivAt.comp x hDm
    have hsurj : Function.Surjective ((π.comp D : Strat k →L[ℝ] Strat k) : Strat k →ₗ[ℝ] Strat k) := by
      intro w
      obtain ⟨A, hA⟩ := hπsurj w
      have hAm : A ∈ LinearMap.range (D : Strat k →ₗ[ℝ] (Fin n → (Strat k →L[ℝ] ℝ))) ⊔ Nstar k := by
        rw [ht]; trivial
      obtain ⟨y, ⟨z, rfl⟩, m, hm, hym⟩ := Submodule.mem_sup.1 hAm
      refine ⟨z, ?_⟩
      have : π A = π (D z) + π m := by rw [← hym, map_add]; rfl
      rw [hπN m hm, add_zero] at this
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, Function.comp_apply]
      rw [← this, hA]
    have hinj := LinearMap.injective_iff_surjective.2 hsurj
    obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz _).1 hinj
    have hne := hG.eventually_ne (c := 0) ⟨K, hK⟩
    filter_upwards [hne] with y hy hyZ
    exact hy (hπN _ hyZ.2)
  -- `Z` is compact.
  have hsimpClosed : ∀ i, IsClosed (simplex (k i)) := by
    intro i
    have : simplex (k i) = (⋂ j, {x : Fin (k i) → ℝ | 0 ≤ x j}) ∩ {x | ∑ j, x j ≤ 1} := by
      ext x; simp [simplex]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j))
      (isClosed_le (by fun_prop) continuous_const)
  have hSclosed : IsClosed (S k) := isClosed_set_pi fun i _ => hsimpClosed i
  have hDcont : ContinuousOn (Dmap u) (S k) := fun x hx =>
    (hDdiff x (hWsubV (hSsubW hx))).continuousAt.continuousWithinAt
  have hZclosed : IsClosed Z :=
    hDcont.preimage_isClosed_of_isClosed hSclosed (Submodule.closed_of_finiteDimensional _)
  have hZc : IsCompact Z :=
    (isCompact_univ_pi hWc).of_isClosed_subset hZclosed (fun x hx => hSsubW hx.1)
  have hZd : IsDiscrete Z := by
    rw [isDiscrete_iff_nhdsNE]
    intro x hx
    rw [inf_principal_eq_bot]
    exact hiso x hx
  have hZfin : Z.Finite := hZc.finite hZd
  refine ⟨hZfin, hZfin.subset ?_⟩
  rintro s ⟨hsN, hsI⟩
  exact ⟨hsN.1, nash_interior_mem_Nstar hn k hk V hVo hSV u hu s hsI hsN⟩
