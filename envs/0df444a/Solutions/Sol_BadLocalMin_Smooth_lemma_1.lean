-- Prove2me | solution 1 for BadLocalMin.Smooth.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T14:42:31.078423+00:00
-- url     : https://prove2.me/submissions/023b071b-cbc9-4a11-a455-1e3ae2578d04

import Mathlib

open Matrix

/-- Lemma 1 (p. 20). Vectors are indexed from 0: the paper's a₁, …, a_{L₁} are `a 0`, …,
`a (L1 - 1)`, so "1 ≤ j ≤ d" is `j.val < d` and "d < j ≤ L₁" is `d ≤ j.val`. -/
theorem solution (L1 L2 d : ℕ) (hL : L1 ≤ L2)
    (a : Fin L1 → Fin L2 → ℝ) (ha : LinearIndependent ℝ a)
    (hd1 : 1 ≤ d) (hdL : d < L1) :
    ∃ u : Fin (L2 - d) → Fin L2 → ℝ, LinearIndependent ℝ u ∧
      ∀ l j, (j.val < d → u l ⬝ᵥ a j = 0) ∧ (d ≤ j.val → 0 < u l ⬝ᵥ a j) := by
  classical
  -- ## The dot-product bilinear form
  let B : LinearMap.BilinForm ℝ (Fin L2 → ℝ) := dotProductBilin ℝ ℝ
  have hB : ∀ x y : Fin L2 → ℝ, B x y = x ⬝ᵥ y := fun x y => rfl
  have hBsymm : B.IsSymm := ⟨fun x y => by rw [hB, hB, dotProduct_comm]⟩
  have hBrefl : B.IsRefl := hBsymm.isRefl
  have hBnd : B.Nondegenerate := by
    constructor
    · intro x hx
      refine dotProduct_eq_zero x fun y => ?_
      simpa [hB] using hx y
    · intro y hy
      refine dotProduct_eq_zero y fun x => ?_
      have h := hy x
      rw [hB, dotProduct_comm] at h
      exact h
  have hfinE : Module.finrank ℝ (Fin L2 → ℝ) = L2 := by
    rw [Module.finrank_pi, Fintype.card_fin]
  -- ## The first `d` vectors span `V`
  let φ : Fin d → Fin L1 := fun i => ⟨i.val, by omega⟩
  have hφinj : Function.Injective φ := fun i j h => Fin.ext (by simpa [φ] using congrArg Fin.val h)
  have haind : LinearIndependent ℝ (fun i : Fin d => a (φ i)) := ha.comp φ hφinj
  let V : Submodule ℝ (Fin L2 → ℝ) := Submodule.span ℝ (Set.range fun i : Fin d => a (φ i))
  have hVfin : Module.finrank ℝ V = d := by
    have h := finrank_span_eq_card haind
    simpa [V, Fintype.card_fin] using h
  -- ## Its orthogonal complement `W`
  let W : Submodule ℝ (Fin L2 → ℝ) := B.orthogonal V
  have hWfin : Module.finrank ℝ W = L2 - d := by
    have h := LinearMap.BilinForm.finrank_orthogonal hBnd V
    rw [hfinE, hVfin] at h
    simpa [W] using h
  -- ## The evaluation map `T x j = a j ⬝ᵥ x`
  let T : (Fin L2 → ℝ) →ₗ[ℝ] (Fin L1 → ℝ) :=
    { toFun := fun x j => B (a j) x
      map_add' := by intro x y; ext j; exact map_add (B (a j)) x y
      map_smul' := by intro c x; ext j; exact map_smul (B (a j)) c x }
  have hkerT : LinearMap.ker T = B.orthogonal (Submodule.span ℝ (Set.range a)) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hx y hy
      refine Submodule.span_induction (p := fun y _ => B y x = 0) ?_ ?_ ?_ ?_ hy
      · rintro z ⟨j, rfl⟩
        have h := congrFun hx j
        simpa [T] using h
      · simp
      · intro u v hu hv ihu ihv
        simp only [map_add, LinearMap.add_apply, ihu, ihv, add_zero]
      · intro c u hu ihu
        simp only [map_smul, LinearMap.smul_apply, ihu, smul_zero]
    · intro hx
      ext j
      exact hx (a j) (Submodule.subset_span ⟨j, rfl⟩)
  have hspanA : Module.finrank ℝ (Submodule.span ℝ (Set.range a)) = L1 := by
    have h := finrank_span_eq_card ha
    simpa [Fintype.card_fin] using h
  have hkerTfin : Module.finrank ℝ (LinearMap.ker T) = L2 - L1 := by
    rw [hkerT, LinearMap.BilinForm.finrank_orthogonal hBnd, hspanA, hfinE]
  have hTrank : Module.finrank ℝ (LinearMap.range T) = L1 := by
    have h := LinearMap.finrank_range_add_finrank_ker T
    rw [hfinE, hkerTfin] at h
    omega
  have hTtop : LinearMap.range T = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hTrank, Module.finrank_pi, Fintype.card_fin]
  have hTsurj : Function.Surjective T := LinearMap.range_eq_top.mp hTtop
  -- ## A vector `u₀` with `a j ⬝ᵥ u₀ = 0` for `j < d` and `= 1` for `d ≤ j`
  let c₀ : Fin L1 → ℝ := fun j => if j.val < d then 0 else 1
  obtain ⟨u₀, hu₀⟩ := hTsurj c₀
  have hu₀_zero : ∀ j : Fin L1, j.val < d → B (a j) u₀ = 0 := by
    intro j hj
    have h := congrFun hu₀ j
    simpa [T, c₀, hj] using h
  have hu₀_one : ∀ j : Fin L1, d ≤ j.val → B (a j) u₀ = 1 := by
    intro j hj
    have h := congrFun hu₀ j
    have hlt : ¬ j.val < d := by omega
    simpa [T, c₀, hlt] using h
  have hu₀W : u₀ ∈ W := by
    show u₀ ∈ B.orthogonal V
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    refine Submodule.span_induction (p := fun v _ => B v u₀ = 0) ?_ ?_ ?_ ?_ hv
    · rintro z ⟨i, rfl⟩
      exact hu₀_zero (φ i) i.isLt
    · simp
    · intro x y hx hy ihx ihy
      simp only [map_add, LinearMap.add_apply, ihx, ihy, add_zero]
    · intro c x hx ih
      simp only [map_smul, LinearMap.smul_apply, ih, smul_zero]
  -- ## The remaining vectors `b k = a (d + k)`
  let ψ : Fin (L1 - d) → Fin L1 := fun k => ⟨d + k.val, by have := k.isLt; omega⟩
  have hψinj : Function.Injective ψ := by
    intro i j h
    simp only [ψ, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  let b : Fin (L1 - d) → (Fin L2 → ℝ) := fun k => a (ψ k)
  have hbind : LinearIndependent ℝ b := by
    have h := ha.comp ψ hψinj
    simpa [b, Function.comp_def] using h
  -- ## The positive cone `C` inside `W`
  let f : Fin (L1 - d) → (Fin L2 → ℝ) → ℝ := fun k u => B (b k) u
  let C : Set W := {u | ∀ k, 0 < f k ((u : W) : Fin L2 → ℝ)}
  have hf_one : ∀ k, f k u₀ = 1 := by
    intro k
    exact hu₀_one (ψ k) (by simp [ψ])
  have hu₀C : (⟨u₀, hu₀W⟩ : W) ∈ C := by
    intro k
    have h1 : f k ((⟨u₀, hu₀W⟩ : W) : Fin L2 → ℝ) = 1 := hf_one k
    rw [h1]
    norm_num
  -- ## For every `z` we can move it into `C` along the `u₀` direction
  have escape : ∀ z : W, ∃ M : ℝ, z + M • (⟨u₀, hu₀W⟩ : W) ∈ C := by
    intro z
    refine ⟨1 + ∑ k : Fin (L1 - d), |f k ((z : W) : Fin L2 → ℝ)|, ?_⟩
    intro k
    have hval : f k (((z + (1 + ∑ k : Fin (L1 - d), |f k ((z : W) : Fin L2 → ℝ)|) •
        (⟨u₀, hu₀W⟩ : W) : W)) : Fin L2 → ℝ)
        = f k ((z : W) : Fin L2 → ℝ) + (1 + ∑ k : Fin (L1 - d), |f k ((z : W) : Fin L2 → ℝ)|) := by
      simp only [f, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, hf_one, smul_eq_mul,
        mul_one]
    rw [hval]
    have hk : |f k ((z : W) : Fin L2 → ℝ)| ≤ ∑ k : Fin (L1 - d), |f k ((z : W) : Fin L2 → ℝ)| :=
      Finset.single_le_sum (f := fun k => |f k ((z : W) : Fin L2 → ℝ)|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ k)
    have hnn : (0:ℝ) ≤ |f k ((z : W) : Fin L2 → ℝ)| := abs_nonneg _
    nlinarith [neg_abs_le (f k ((z : W) : Fin L2 → ℝ))]
  -- ## `C` is not contained in any proper subspace of `W`
  have hC_not_subset : ∀ S : Submodule ℝ W, S ≠ ⊤ → ∃ u ∈ C, u ∉ S := by
    intro S hS
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hu₀S : (⟨u₀, hu₀W⟩ : W) ∈ S := h _ hu₀C
    apply hS
    rw [eq_top_iff]
    intro z _
    obtain ⟨M, hM⟩ := escape z
    have h1 : z + M • (⟨u₀, hu₀W⟩ : W) ∈ S := h _ hM
    have h2 : M • (⟨u₀, hu₀W⟩ : W) ∈ S := S.smul_mem M hu₀S
    have h3 := S.sub_mem h1 h2
    simpa using h3
  -- ## Inductively build `L2 - d` independent vectors in `C`
  have key : ∀ k : ℕ, k ≤ L2 - d → ∃ v : Fin k → W, (∀ i, v i ∈ C) ∧ LinearIndependent ℝ v := by
    intro k hk
    induction k with
    | zero =>
        exact ⟨Fin.elim0, fun i => i.elim0, by
          rw [linearIndependent_iff']
          intro s g hs i hi
          exact i.elim0⟩
    | succ k ih =>
        obtain ⟨v, hvC, hvind⟩ := ih (by omega)
        have hspanfin : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = k := by
          have h := finrank_span_eq_card hvind
          simpa [Fintype.card_fin] using h
        have hSne : Submodule.span ℝ (Set.range v) ≠ ⊤ := by
          intro htop
          have h2 : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = Module.finrank ℝ W := by
            rw [htop]
            exact finrank_top ℝ W
          rw [hspanfin, hWfin] at h2
          omega
        obtain ⟨u, huC, huS⟩ := hC_not_subset _ hSne
        refine ⟨Fin.snoc (α := fun _ => W) v u, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · simpa using huC
          · intro j
            simpa using hvC j
        · exact LinearIndependent.finSnoc hvind huS
  obtain ⟨v, hvC, hvind⟩ := key (L2 - d) le_rfl
  -- ## Assemble the answer
  refine ⟨fun l => ((v l : W) : Fin L2 → ℝ), ?_, ?_⟩
  · have hcoe : (fun l => ((v l : W) : Fin L2 → ℝ)) = (Submodule.subtype W) ∘ v := rfl
    rw [hcoe]
    exact hvind.map' (Submodule.subtype W) (Submodule.ker_subtype W)
  · intro l j
    constructor
    · intro hj
      have hmem : ((v l : W) : Fin L2 → ℝ) ∈ B.orthogonal V := (v l).2
      have haV : a j ∈ V := by
        have hj' : j = φ ⟨j.val, hj⟩ := Fin.ext rfl
        rw [hj']
        exact Submodule.subset_span ⟨⟨j.val, hj⟩, rfl⟩
      have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hmem) (a j) haV
      have h2 : B ((v l : W) : Fin L2 → ℝ) (a j) = 0 := by
        rw [hBsymm.eq]
        exact h1
      rw [← hB]
      exact h2
    · intro hj
      let k : Fin (L1 - d) := ⟨j.val - d, by omega⟩
      have hψk : ψ k = j := by
        apply Fin.ext
        show d + (j.val - d) = j.val
        omega
      have hmemC := hvC l k
      have hfk : f k ((v l : W) : Fin L2 → ℝ) = B (b k) ((v l : W) : Fin L2 → ℝ) := rfl
      have hbk : b k = a j := by simp [b, hψk]
      rw [hfk, hbk] at hmemC
      rw [← hB]
      rw [hBsymm.eq]
      exact hmemC
