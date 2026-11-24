-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.dual_vector_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:34.606397+00:00
-- url     : https://prove2.me/submissions/1f8ddecb-1be9-4dc3-af31-4f7a878fe9f9

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gi_adj_last
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gi_sesq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
open scoped ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.DualVectorNormSq := by
  intro V _ _ h hh r y f' T T' hT' hy hf x0 om al hx0 hom hx
  set M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun a b => h (y a) (f' b) with hM
  set L := Fin.last r with hL

  have hA : ∀ x ∈ Submodule.span ℂ (f' '' {b | b ≠ L}), ∀ b, h x (f' b) = 0 := by
    intro x hx b
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      rw [hf, if_neg (fun hh => hc hh.1)]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have hB : ∀ u : V, (∀ b, h u (f' b) = 0) → ∀ x ∈ Submodule.span ℂ (f' '' {b | b ≠ L}), h u x = 0 := by
    intro u hu x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, _, rfl⟩ := hx
      exact hu c
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have e00 : h x0 x0 = 0 := hB x0 (hA x0 hx0) x0 hx0
  have e0f : h x0 (f' L) = 0 := hA x0 hx0 L
  have ef0 : h (f' L) x0 = 0 := by rw [hh, e0f, map_zero]
  have eo0 : h om x0 = 0 := hB om hom x0 hx0
  have e0o : h x0 om = 0 := by rw [hh, eo0, map_zero]
  have eof : h om (f' L) = 0 := hom L
  have efo : h (f' L) om = 0 := by rw [hh, eof, map_zero]
  have eff : h (f' L) (f' L) = -(T' : ℂ) := by rw [hf, if_pos ⟨rfl, rfl⟩]
  set x' : V := ∑ a, M.adjugate L a • y a with hx'

  have p1 : h x' (f' L) = M.det := by
    have : h x' (f' L) = (M.adjugate * M) L L := by
      rw [hx', Matrix.mul_apply, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rfl
    rw [this, Matrix.adjugate_mul]
    simp
  have p2 : h x' (f' L) = al * -(T' : ℂ) := by
    rw [hx]
    simp [e0f, eof, eff]

  have n1 : h x' x' = M.adjugate L L * conj (M.adjugate L L) * -(T : ℂ) := by
    rw [hx', gi_sesq_sum, Finset.sum_eq_single L, Finset.sum_eq_single L]
    · rw [hy, if_pos ⟨rfl, rfl⟩]
    · intro a _ ha
      rw [hy, if_neg (fun hh => ha hh.1), mul_zero]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [hy, if_neg (fun hh => hb hh.2), mul_zero]
    · simp
  have n2 : h x' x' = al * conj al * -(T' : ℂ) + h om om := by
    rw [hx]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, e00, e0f, ef0,
      eo0, e0o, eof, efo, eff, smul_eq_mul]
    ring
  have hT'c : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'
  have hal : al = - M.det / (T' : ℂ) := by
    field_simp
    linear_combination p2 - p1
  rw [gi_adj_last] at n1
  have hcT : conj (T' : ℂ) = (T' : ℂ) := Complex.conj_ofReal T'
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  have key : h om om = leadingPrincipalMinor M r * conj (leadingPrincipalMinor M r) * -(T : ℂ) - al * conj al * -(T' : ℂ) := by
    linear_combination n1 - n2
  rw [key, hal]
  simp only [map_div₀, map_neg, hcT]
  field_simp
  ring
end Formalism.HermitianLatticeCounting.P
