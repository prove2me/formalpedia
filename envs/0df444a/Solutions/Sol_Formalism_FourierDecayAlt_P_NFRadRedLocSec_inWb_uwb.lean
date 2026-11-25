-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.inWb_uwb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:34.034503+00:00
-- url     : https://prove2.me/submissions/31ea082c-5b31-4f6b-9a2b-c20a8be90fe2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH
import Theorems.Thm_Formalism_QuantumDeterminants_gn_herm_bvec_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Trans
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
variable {H}
end Trans
section Smooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X} {m : ℕ}
end Smooth
section Main
variable {k r : ℕ}
private lemma hpk_apply_of_outer_index (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    Hpk k r i j = if i.val + j.val = 2 * r + k then 1 else 0 := by
  simp only [Hpk]
  split_ifs <;> first | rfl | (exfalso; omega)
private lemma hpk_mulVec_apply_of_outer_index (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hi : i.val < r ∨ r + k < i.val) : (Hpk k r *ᵥ v) i = v ⟨2 * r + k - i.val, by omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, fun j => hpk_apply_of_outer_index (k := k) (r := r) i j hi]
  rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
  · rw [if_pos (Nat.add_sub_cancel' (by omega)), one_mul]
  · intro l _ hl
    rw [if_neg, zero_mul]
    intro h
    exact hl (Fin.ext (by show l.val = 2 * r + k - i.val; omega))
  · intro h
    exact absurd (Finset.mem_univ _) h
variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
end Main
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedLocSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
theorem _root_.solution {g : Q.Mx k r} (hg : g ∈ B2.UWb k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (g *ᵥ v) := by
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  intro i hi
  obtain ⟨j, hjv⟩ : ∃ j : Fin (2 * r + k + 1), j.val = 2 * r + k - i.val := ⟨⟨_, by omega⟩, rfl⟩
  have hjo : j.val < r ∨ r + k < j.val := by omega
  have hji : (⟨2 * r + k - j.val, by omega⟩ : Fin (2 * r + k + 1)) = i :=
    Fin.ext (by show 2 * r + k - j.val = i.val; omega)
  have hfix : g *ᵥ bvec j = bvec j := by
    rcases Nat.lt_or_ge j.val r with h | h
    · have e : eI k r ⟨j.val, h⟩ = j := Fin.ext rfl
      rw [← e]
      exact (hg'.2 _).1
    · have ha : i.val < r := by omega
      have e : esI k r ⟨i.val, ha⟩ = j := Fin.ext (by show 2 * r + k - i.val = j.val; omega)
      rw [← e]
      exact (hg'.2 _).2
  have e1 : (g *ᵥ v) i = (Hpk k r *ᵥ (g *ᵥ v)) j := by rw [hpk_mulVec_apply_of_outer_index _ j hjo, hji]
  rw [e1, ← gn_herm_bvec_right, ← hfix, TwoByOneBlock.herm_UH hg'.1, gn_herm_bvec_right, hpk_mulVec_apply_of_outer_index _ j hjo, hji]
  exact hv i hi
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
