-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.affine_fibre_count_comparison
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:59.233044+00:00
-- url     : https://prove2.me/submissions/993dc336-9c59-44f7-99d3-de522bee9224

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_card_fiber_eq
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_card_fiber_prod
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_card_slice
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_card_ker
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_mem_range_iff_dual
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_pow_pred_of_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
theorem _root_.solution : Formalism.HermitianLattices.RamifiedLatticeOperators.AffineFibreCountComparison := by
  intro F _ _ n g xb f uW
  classical
  dsimp only
  set q := Fintype.card F with hqdef
  have hq1 : 1 < q := Fintype.one_lt_card
  set M := LinearMap.toMatrix' xb with hM
  have hxbM : M.mulVecLin = xb := by rw [hM, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hxb : ∀ l, xb l = M *ᵥ l := fun l => by rw [← hxbM]; rfl
  let T : (Fin (n + g) → F) →ₗ[F] (Fin n → F) := Mᵀ.mulVecLin
  have hTw : ∀ w, T w = w ᵥ* M := fun w => Matrix.mulVec_transpose M w
  have hcond : ∀ (w : Fin (n + g) → F) (f' : Fin n → F),
      (∀ l, w ⬝ᵥ xb l = f' ⬝ᵥ l) ↔ T w = f' := by
    intro w f'
    constructor
    · intro h; funext j
      have h1 := h (Pi.single j 1)
      rw [hxb, dotProduct_mulVec, dotProduct_single, dotProduct_single, mul_one, mul_one] at h1
      rw [hTw]; exact h1
    · intro h l; rw [hxb, dotProduct_mulVec, ← hTw, h]
  set rk := finrank F (LinearMap.range xb) with hrk
  have hrkT : finrank F (LinearMap.range T) = rk := by
    have h1 := Matrix.rank_transpose M
    unfold Matrix.rank at h1
    rw [hxbM] at h1
    exact h1
  have hrkle : rk ≤ n := by
    have h1 := LinearMap.finrank_range_le xb
    simpa using h1
  have hkerT : Nat.card {w : Fin (n + g) → F // T w = 0} = q ^ (n + g - rk) := by
    rw [card_ker]; congr 1
    have h1 := LinearMap.finrank_range_add_finrank_ker T
    rw [hrkT, Module.finrank_fin_fun] at h1; omega
  have hkerx : Nat.card {u : Fin n → F // xb u = 0} = q ^ (n - rk) := by
    rw [card_ker]; congr 1
    have h1 := LinearMap.finrank_range_add_finrank_ker xb
    rw [Module.finrank_fin_fun] at h1; omega
  have hfker : (∀ l ∈ LinearMap.ker xb, f ⬝ᵥ l = 0) ↔ f ∈ LinearMap.range T := by
    have h1 := mem_range_iff_dual Mᵀ f
    rw [Matrix.transpose_transpose] at h1
    rw [show f ∈ LinearMap.range T ↔ f ∈ LinearMap.range Mᵀ.mulVecLin from Iff.rfl, h1]
    constructor
    · intro h w hw
      rw [dotProduct_comm]; exact h w (by rw [LinearMap.mem_ker, hxb]; exact hw)
    · intro h l hl
      rw [dotProduct_comm]; exact h l (by rw [← hxb]; exact LinearMap.mem_ker.mp hl)
  have huW : uW ∈ LinearMap.range xb ↔ ∀ w, T w = 0 → w ⬝ᵥ uW = 0 := by
    have h1 := mem_range_iff_dual M uW
    rw [hxbM] at h1
    exact h1
  let ψ : (Fin (n + g) → F) →ₗ[F] F :=
    { toFun := fun w => w ⬝ᵥ uW, map_add' := fun a b => add_dotProduct a b uW,
      map_smul' := fun c a => smul_dotProduct c a uW }
  let χ : (Fin n → F) →ₗ[F] F :=
    { toFun := fun u => f ⬝ᵥ u, map_add' := fun a b => dotProduct_add f a b,
      map_smul' := fun c a => dotProduct_smul c f a }
  have hA : Nat.card {fW : Fin (n + g) → F // fW ⬝ᵥ uW = 1 ∧ ∀ l, fW ⬝ᵥ xb l = f ⬝ᵥ l} =
      Nat.card {w // T w = f ∧ ψ w = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by rw [hcond]; exact and_comm)
  have hB : Nat.card {u : Fin n → F // f ⬝ᵥ u = 1 ∧ xb u = uW} =
      Nat.card {u // xb u = uW ∧ χ u = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u => and_comm)
  rw [hA, hB]
  have zeroA : f ∉ LinearMap.range T → Nat.card {w // T w = f ∧ ψ w = 1} = 0 := fun h =>
    Nat.card_eq_zero.mpr (Or.inl ⟨fun x => h ⟨x.1, x.2.1⟩⟩)
  have zeroB : uW ∉ LinearMap.range xb → Nat.card {u // xb u = uW ∧ χ u = 1} = 0 := fun h =>
    Nat.card_eq_zero.mpr (Or.inl ⟨fun x => h ⟨x.1, x.2.1⟩⟩)
  have halfA : f ∈ LinearMap.range T → uW ∉ LinearMap.range xb →
      q * Nat.card {w // T w = f ∧ ψ w = 1} = q ^ (n + g - rk) := by
    rintro ⟨w0, hw0⟩ hu
    rw [huW] at hu; push Not at hu
    obtain ⟨s, hs, hψs⟩ := hu
    have hψs' : ψ s ≠ 0 := hψs
    rw [card_fiber_prod T ψ (w0 + ((1 - ψ w0) / ψ s) • s) f 1
      (by rw [map_add, map_smul, hs, smul_zero, add_zero, hw0])
      (by rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hψs']; ring),
      card_slice T ψ s hs hψs' 0, hkerT]
  have halfB : uW ∈ LinearMap.range xb → ¬ (∀ l ∈ LinearMap.ker xb, f ⬝ᵥ l = 0) →
      q * Nat.card {u // xb u = uW ∧ χ u = 1} = q ^ (n - rk) := by
    rintro ⟨u0, hu0⟩ hf
    push Not at hf
    obtain ⟨s, hs, hχs⟩ := hf
    rw [LinearMap.mem_ker] at hs
    have hχs' : χ s ≠ 0 := hχs
    rw [card_fiber_prod xb χ (u0 + ((1 - χ u0) / χ s) • s) uW 1
      (by rw [map_add, map_smul, hs, smul_zero, add_zero, hu0])
      (by rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hχs']; ring),
      card_slice xb χ s hs hχs' 0, hkerx]
  have fullA : ∀ u0, xb u0 = uW → f ∈ LinearMap.range T →
      Nat.card {w // T w = f ∧ ψ w = 1} = if f ⬝ᵥ u0 = 1 then q ^ (n + g - rk) else 0 := by
    rintro u0 hu0 ⟨w0, hw0⟩
    have hval : ∀ w, T w = f → ψ w = f ⬝ᵥ u0 := by
      intro w hw
      show w ⬝ᵥ uW = f ⬝ᵥ u0
      rw [← hu0, hxb, dotProduct_mulVec, ← hTw, hw]
    split_ifs with h1
    · rw [← hkerT, ← card_fiber_eq T w0, hw0]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun w =>
        ⟨fun h => h.1, fun h => ⟨h, by rw [hval w h, h1]⟩⟩)
    · exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => h1 ((hval x.1 x.2.1).symm.trans x.2.2)⟩)
  have fullB : ∀ u0, xb u0 = uW → (∀ l ∈ LinearMap.ker xb, f ⬝ᵥ l = 0) →
      Nat.card {u // xb u = uW ∧ χ u = 1} = if f ⬝ᵥ u0 = 1 then q ^ (n - rk) else 0 := by
    intro u0 hu0 hf
    have hval : ∀ u, xb u = uW → χ u = f ⬝ᵥ u0 := by
      intro u hu
      have hk : u - u0 ∈ LinearMap.ker xb := by
        rw [LinearMap.mem_ker, map_sub, hu, hu0, sub_self]
      have h2 := hf _ hk
      show f ⬝ᵥ u = f ⬝ᵥ u0
      rw [dotProduct_sub, sub_eq_zero] at h2; exact h2
    split_ifs with h1
    · rw [← hkerx, ← card_fiber_eq xb u0, hu0]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun u =>
        ⟨fun h => h.1, fun h => ⟨h, by rw [hval u h, h1]⟩⟩)
    · exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => h1 ((hval x.1 x.2.1).symm.trans x.2.2)⟩)
  refine ⟨fun hu hf => ?_, fun hu hf => ?_, fun hu hf => ?_, fun hu hf => ?_⟩
  · rw [zeroB hu]
    obtain ⟨_, h2⟩ := pow_pred_of_mul hq1 (halfA (hfker.mp hf) hu)
    rw [h2]; push_cast; ring
  · rw [zeroA (fun h => hf (hfker.mpr h))]
    obtain ⟨he, h2⟩ := pow_pred_of_mul hq1 (halfB hu hf)
    rw [h2]; push_cast
    have e : n + g - rk - 1 = g + (n - rk - 1) := by omega
    rw [e, pow_add]; ring
  · obtain ⟨u0, hu0⟩ := hu
    rw [fullA u0 hu0 (hfker.mp hf), fullB u0 hu0 hf]
    have e : n + g - rk = g + (n - rk) := by omega
    split_ifs
    · push_cast; rw [e, pow_add]; ring
    · push_cast; ring
  · rw [zeroA (fun h => hf (hfker.mpr h)), zeroB hu]; simp
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
