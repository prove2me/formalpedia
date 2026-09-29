-- Prove2me | solution 1 for ContinuousLinearMap.exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5b7bf0ee-bbec-5b39-b327-269f113506b9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass

set_option autoImplicit false

open MeasureTheory

theorem solution
    (d : ℕ) (XK : Set (Fin d → ℂ × ℂ))
    (emb : C((Fin d → AddCircle (1 : ℝ)), XK))
    (hemb : ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d),
      ((emb θ : XK) : Fin d → ℂ × ℂ) i = ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))
    (μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ)
    (hμ : ∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) :
    ∃ Λ : C(XK, ℂ) →L[ℂ] ℂ,
      (∀ h : C(XK, ℂ), Λ h = μ (h.comp emb)) ∧
      ∀ (τ : Fin d → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : Fin d → Set (ℂ × ℂ),
        (∀ v ∈ (Finset.univ : Finset (Fin d)), IsOpen (U v) ∧ τ v ∈ U v) ∧
        ∀ g : C(XK, ℂ), (∀ y : XK, (∃ v ∈ (Finset.univ : Finset (Fin d)), (y : Fin d → ℂ × ℂ) v ∉ U v) → g y = 0) →
          (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε := by
  classical

  let compCLM : C(XK, ℂ) →L[ℂ] C((Fin d → AddCircle (1 : ℝ)), ℂ) :=
    { toFun := fun h => h.comp emb
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := ContinuousMap.continuous_precomp emb }
  refine ⟨μ.comp compCLM, fun h => rfl, ?_⟩
  intro τ ε hε

  let F : AddCircle (1 : ℝ) → ℂ × ℂ := fun t => ((fourier 1 t : ℂ), (fourier (-1) t : ℂ))
  have hFc : Continuous F := (fourier 1).continuous.prodMk (fourier (-1)).continuous
  have hFi : Function.Injective F := by
    intro a b h
    have h1 : (fourier 1 a : ℂ) = fourier 1 b := congrArg Prod.fst h
    rw [fourier_one, fourier_one] at h1
    exact AddCircle.injective_toCircle one_ne_zero (by exact_mod_cast h1)

  let τ' : Fin d → AddCircle (1 : ℝ) := fun i => if h : ∃ t, F t = τ i then h.choose else 0
  obtain ⟨U', hU'o, hU'g⟩ := hμ τ' ε hε

  let S : Fin d → Set (AddCircle (1 : ℝ)) := fun i => if (∃ t, F t = τ i) then (U' i)ᶜ else Set.univ
  have hSc : ∀ i, IsClosed (S i) := by
    intro i
    by_cases h : ∃ t, F t = τ i
    · simp only [S, if_pos h]; exact (hU'o i).1.isClosed_compl
    · simp only [S, if_neg h]; exact isClosed_univ
  have hSU : ∀ (i : Fin d) (t : AddCircle (1 : ℝ)), t ∉ S i → t ∈ U' i := by
    intro i t ht
    by_cases h : ∃ t, F t = τ i
    · simp only [S, if_pos h, Set.mem_compl_iff, not_not] at ht; exact ht
    · simp only [S, if_neg h, Set.mem_univ, not_true_eq_false] at ht
  refine ⟨fun i => (F '' S i)ᶜ, ?_, ?_⟩
  · intro i _
    refine ⟨((hSc i).isCompact.image hFc).isClosed.isOpen_compl, ?_⟩
    simp only [Set.mem_compl_iff]
    rintro ⟨t, ht, hti⟩
    by_cases h : ∃ t, F t = τ i
    · have hτ' : F (τ' i) = τ i := by simp only [τ', dif_pos h]; exact h.choose_spec
      have htt : t = τ' i := hFi (hti.trans hτ'.symm)
      simp only [S, if_pos h, Set.mem_compl_iff] at ht
      exact ht (htt ▸ (hU'o i).2)
    · exact h ⟨t, hti⟩
  · intro g hg0 hg1
    show ‖μ (g.comp emb)‖ < ε
    refine hU'g (g.comp emb) ?_ (fun θ => hg1 (emb θ))
    rintro θ ⟨i, hi⟩
    show g (emb θ) = 0
    apply hg0
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [hemb]
    simp only [Set.mem_compl_iff, not_not]
    refine ⟨θ i, ?_, rfl⟩
    by_contra hS
    exact hi (hSU i (θ i) hS)

end S_ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass
end P2MW
export P2MW.S_ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass (solution)
