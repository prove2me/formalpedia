-- Prove2me | solution 1 for CGWH.cofiniteTopology_not_weaklyHausdorffSpace
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:50:37.24007+00:00
-- url     : https://prove2.me/submissions/a47500bb-31c9-444a-b75f-4485c6020629

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_cofiniteTopology_not_weaklyHausdorffSpace

open CGWH

theorem isClosed_cg_iff {X : Type u} [TopologicalSpace X] (s : Set X) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} X] s ↔
      ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (f : K → X),
        Continuous f → IsClosed (f ⁻¹' s) := by
  simp only [isClosed_coinduced, isClosed_sigma_iff, Sigma.forall]
  constructor
  · intro h K _ _ _ f hf; exact h (CompHaus.of K) ⟨f, hf⟩
  · intro h S f; exact h S f f.2

end Sol_CGWH_cofiniteTopology_not_weaklyHausdorffSpace

open CGWH Sol_CGWH_cofiniteTopology_not_weaklyHausdorffSpace

theorem solution (X : Type u) [Infinite X] :
    ¬ WeaklyHausdorffSpace (CofiniteTopology X) ∧
      ¬ IsClosed[TopologicalSpace.compactlyGenerated.{u}
          (CofiniteTopology X × CofiniteTopology X)] (Set.diagonal (CofiniteTopology X)) := by
  let e : ℕ ↪ X := Infinite.natEmbedding X
  have hcont : ∀ (φ : ULift.{u} (OnePoint ℕ) → CofiniteTopology X),
      Function.Injective φ → Continuous φ := by
    intro φ hφ
    rw [continuous_iff_isClosed]
    intro s hs
    rcases CofiniteTopology.isClosed_iff.mp hs with rfl | hfin
    · simp
    · exact (hfin.preimage hφ.injOn).isClosed
  let g1 : ULift.{u} (OnePoint ℕ) → CofiniteTopology X :=
    fun k => CofiniteTopology.of (k.down.elim (e 0) (fun n => e (n + 2)))
  let g2 : ULift.{u} (OnePoint ℕ) → CofiniteTopology X :=
    fun k => CofiniteTopology.of (k.down.elim (e 1) (fun n => e (n + 2)))
  have hinj : ∀ a : ℕ, a ≤ 1 → Function.Injective
      (fun k : ULift.{u} (OnePoint ℕ) =>
        CofiniteTopology.of (k.down.elim (e a) (fun n => e (n + 2)))) := by
    intro a ha
    rintro ⟨x⟩ ⟨y⟩ hxy
    have hxy' := CofiniteTopology.of.injective hxy
    congr 1
    induction x using OnePoint.rec with
    | infty =>
      induction y using OnePoint.rec with
      | infty => rfl
      | coe n =>
        simp only [OnePoint.elim_infty, OnePoint.elim_some, e.apply_eq_iff_eq] at hxy'
        omega
    | coe m =>
      induction y using OnePoint.rec with
      | infty =>
        simp only [OnePoint.elim_infty, OnePoint.elim_some, e.apply_eq_iff_eq] at hxy'
        omega
      | coe n =>
        simp only [OnePoint.elim_some, e.apply_eq_iff_eq] at hxy'
        have : m = n := by omega
        rw [this]
  have hg1 : Function.Injective g1 := hinj 0 (by omega)
  have hg2 : Function.Injective g2 := hinj 1 (by omega)
  constructor
  · intro hWH
    have hcl := hWH.isClosed_range (ULift.{u} (OnePoint ℕ)) g1 (hcont g1 hg1)
    rcases CofiniteTopology.isClosed_iff.mp hcl with huniv | hfin
    · have : CofiniteTopology.of (e 1) ∈ Set.range g1 := by rw [huniv]; trivial
      obtain ⟨⟨k⟩, hk⟩ := this
      have hk' := CofiniteTopology.of.injective hk
      induction k using OnePoint.rec with
      | infty =>
        simp only [OnePoint.elim_infty, e.apply_eq_iff_eq] at hk'
        omega
      | coe n =>
        simp only [OnePoint.elim_some, e.apply_eq_iff_eq] at hk'
        omega
    · exact Set.infinite_range_of_injective hg1 hfin
  · intro h
    rw [isClosed_cg_iff] at h
    have hcl := h (ULift.{u} (OnePoint ℕ)) (fun k => (g1 k, g2 k))
      ((hcont g1 hg1).prodMk (hcont g2 hg2))
    have hset : (fun k => (g1 k, g2 k)) ⁻¹' Set.diagonal (CofiniteTopology X) =
        ULift.down ⁻¹' Set.range ((↑) : ℕ → OnePoint ℕ) := by
      ext ⟨k⟩
      simp only [Set.mem_preimage, Set.mem_diagonal_iff, g1, g2]
      induction k using OnePoint.rec with
      | infty =>
        simp only [OnePoint.elim_infty, EmbeddingLike.apply_eq_iff_eq, e.apply_eq_iff_eq]
        simp
      | coe n => simp
    rw [hset] at hcl
    have hcl2 : IsClosed (Set.range ((↑) : ℕ → OnePoint ℕ)) := by
      have := hcl.preimage (continuous_uliftUp (X := OnePoint ℕ))
      simpa [Set.preimage_preimage] using this
    have hd : Dense (Set.range ((↑) : ℕ → OnePoint ℕ)) := OnePoint.denseRange_coe
    have := hcl2.closure_eq ▸ hd.closure_eq
    have hmem : (OnePoint.infty : OnePoint ℕ) ∈ Set.range ((↑) : ℕ → OnePoint ℕ) := by
      rw [this]; trivial
    obtain ⟨n, hn⟩ := hmem
    exact OnePoint.coe_ne_infty n hn
