-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gsK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:29.439499+00:00
-- url     : https://prove2.me/submissions/2ba2e00b-e98c-4449-9005-4b544791238d

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (h : U →ₗ[K] U →ₗ⋆[K] K) (herm : ∀ x y : U, star (h x y) = h y x)
    (haniso : ∀ x : U, h x x = 0 → x = 0) :
    ∀ (s : ℕ) (w : Fin s → U), ∃ (g : Fin s → U) (L : Matrix (Fin s) (Fin s) K), L.det = 1 ∧
      (∀ b, w b = ∑ c, L b c • g c) ∧ (∀ a b, a ≠ b → h (g a) (g b) = 0) := by
  intro s
  induction s with
  | zero => intro w; exact ⟨fun a => a.elim0, 1, by simp, fun b => b.elim0, fun a => a.elim0⟩
  | succ s ih =>
    intro w
    obtain ⟨g₀, L₀, hdet, hw₀, horth⟩ := ih (fun b => w b.castSucc)
    let t : Fin s → K := fun c => h (w (Fin.last s)) (g₀ c) / h (g₀ c) (g₀ c)
    let gl : U := w (Fin.last s) - ∑ c, t c • g₀ c
    let g : Fin (s + 1) → U := Fin.lastCases (motive := fun _ => U) gl g₀
    let L : Matrix (Fin (s + 1)) (Fin (s + 1)) K := Matrix.of fun b c =>
      Fin.lastCases (motive := fun _ => K) (Fin.lastCases (motive := fun _ => K) 1 t c)
        (fun b' => Fin.lastCases (motive := fun _ => K) 0 (L₀ b') c) b
    have hgc : ∀ c, g c.castSucc = g₀ c := by intro c; simp [g]
    have hgl : g (Fin.last s) = gl := by simp [g]
    have hLcc : ∀ b c, L b.castSucc c.castSucc = L₀ b c := by intro b c; simp [L]
    have hLcl : ∀ b : Fin s, L b.castSucc (Fin.last s) = 0 := by intro b; simp [L]
    have hLlc : ∀ c : Fin s, L (Fin.last s) c.castSucc = t c := by intro c; simp [L]
    have hLll : L (Fin.last s) (Fin.last s) = 1 := by simp [L]
    have hglo : ∀ b, h gl (g₀ b) = 0 := by
      intro b
      simp only [gl, map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single b]
      · by_cases h0 : h (g₀ b) (g₀ b) = 0
        · have := haniso _ h0
          simp [this]
        · simp only [t]; rw [div_mul_cancel₀ _ h0, sub_self]
      · intro c _ hc; rw [horth c b hc, mul_zero]
      · intro hb; exact absurd (Finset.mem_univ b) hb
    refine ⟨g, L, ?_, ?_, ?_⟩
    · rw [Matrix.det_succ_column L (Fin.last s), Fin.sum_univ_castSucc]
      simp only [hLcl, hLll, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, mul_one]
      have e : (L.submatrix (Fin.last s).succAbove (Fin.last s).succAbove) = L₀ := by
        ext a b; simp [Fin.succAbove_last, hLcc]
      have e2 : ((-1 : K)) ^ ((Fin.last s : Fin (s+1)).val + (Fin.last s : Fin (s+1)).val) = 1 := by
        rw [← two_mul, pow_mul]; simp
      rw [e, hdet, e2, one_mul]
    · intro b
      refine Fin.lastCases ?_ (fun b' => ?_) b
      · rw [Fin.sum_univ_castSucc]
        simp only [hLlc, hLll, hgc, hgl, one_smul]
        simp [gl]
      · rw [Fin.sum_univ_castSucc]
        simp only [hLcc, hLcl, hgc, zero_smul, add_zero]
        exact hw₀ b'
    · intro a b hab
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · rw [hgc, hgc]; exact horth a' b' (fun e => hab (by rw [e]))
      · rw [hgc, hgl, ← herm, hglo, star_zero]
      · rw [hgl, hgc]; exact hglo b'
      · exact absurd rfl hab
end Formalism.HermitianLatticeCounting.P
