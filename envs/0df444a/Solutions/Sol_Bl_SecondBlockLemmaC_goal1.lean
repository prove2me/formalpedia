-- Prove2me | solution 1 for Bl.SecondBlockLemmaC.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:25.120288+00:00
-- url     : https://prove2.me/submissions/47420244-9a60-4a49-90dd-c1c1ad33d09c

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasB_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open Bl Bl.SecondBlockLemmaC
namespace Bl.SecondBlockLemmaC
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ s : Set G, MeasurableSet s ∧ ∀ μ : Measure G, IsFundamentalDomain Γ s μ := by
  classical
  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Γ))
  have h1U : (1 : G) ∈ U := by
    have h : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' U := by rw [hU]; rfl
    simpa using h
  obtain ⟨V, hVo, h1V, hV⟩ := exists_open_nhds_one_split (hUo.mem_nhds h1U)
  set W : Set G := V ∩ V⁻¹ with hW
  have hWo : IsOpen W := hVo.inter hVo.inv
  have h1W : (1 : G) ∈ W := ⟨h1V, by simpa using h1V⟩
  have key : ∀ a ∈ W, ∀ b ∈ W, ∀ γ : Γ, (γ : G) = b * a⁻¹ → γ = 1 := by
    intro a ha b hb γ hγ
    have h2 : a⁻¹ ∈ V := by simpa using ha.2
    have h3 : (γ : G) ∈ U := hγ ▸ hV b hb.1 a⁻¹ h2
    have h4 : γ ∈ ((↑) : Γ → G) ⁻¹' U := h3
    rw [hU] at h4
    exact h4
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq G
  let Q : G → ℕ → Prop := fun x n => ∃ γ : Γ, (γ : G) * x * (u n)⁻¹ ∈ W
  have hQinv : ∀ (δ : Γ) (x : G) (n : ℕ), Q ((δ : G) * x) n ↔ Q x n := by
    intro δ x n
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨γ * δ, by simpa [mul_assoc] using hγ⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨γ * δ⁻¹, by simpa [mul_assoc] using hγ⟩
  have hQex : ∀ x, ∃ n, Q x n := by
    intro x
    obtain ⟨n, hn⟩ := hu.exists_mem_open (s := {g | x * g⁻¹ ∈ W})
      (hWo.preimage (by fun_prop)) ⟨x, by simpa using h1W⟩
    exact ⟨n, 1, by simpa using hn⟩
  let s : Set G := {x | ∃ n, x * (u n)⁻¹ ∈ W ∧ ∀ m < n, ¬ Q x m}
  have hs : s = ⋃ n, ({x | x * (u n)⁻¹ ∈ W} ∩
      ⋂ m, ⋂ (_ : m < n), (⋃ γ : Γ, {x | (γ : G) * x * (u m)⁻¹ ∈ W})ᶜ) := by
    ext x
    simp [s, Q]
  have hsm : MeasurableSet s := by
    rw [hs]
    refine MeasurableSet.iUnion fun n => ?_
    refine MeasurableSet.inter (hWo.preimage (by fun_prop)).measurableSet ?_
    refine MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => ?_
    refine MeasurableSet.compl ?_
    exact (isOpen_iUnion fun γ => hWo.preimage (by fun_prop)).measurableSet
  refine ⟨s, hsm, fun μ => IsFundamentalDomain.mk' hsm.nullMeasurableSet fun x => ?_⟩
  obtain ⟨γ, hγ⟩ := Nat.find_spec (hQex x)
  refine ⟨γ, ?_, ?_⟩
  · change (γ : G) * x ∈ s
    refine ⟨Nat.find (hQex x), hγ, fun m hm => ?_⟩
    rw [hQinv]
    exact Nat.find_min (hQex x) hm
  · intro δ hδ
    change (δ : G) * x ∈ s at hδ
    obtain ⟨k, hk, hkmin⟩ := hδ
    have hQk : Q x k := ⟨δ, by simpa [mul_assoc] using hk⟩
    have hle : Nat.find (hQex x) ≤ k := Nat.find_min' (hQex x) hQk
    have hk' : k = Nat.find (hQex x) := by
      rcases Nat.lt_or_ge (Nat.find (hQex x)) k with h | h
      · exact absurd ((hQinv δ x _).mpr (Nat.find_spec (hQex x))) (hkmin _ h)
      · omega
    rw [hk'] at hk
    have hd : ((δ * γ⁻¹ : Γ) : G) = ((δ : G) * x * (u (Nat.find (hQex x)))⁻¹) *
        ((γ : G) * x * (u (Nat.find (hQex x)))⁻¹)⁻¹ := by
      simp [mul_assoc]
    have h1 := key _ hγ _ hk _ hd
    exact mul_inv_eq_one.mp h1
end Bl.SecondBlockLemmaC
