-- Prove2me | solution 1 for CuspForm.intLattice_fg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f8db8fa1-c817-5099-a72b-c03eaf00dacc

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_ModularForm_sturm_bound_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_intLattice_fg

set_option autoImplicit false

noncomputable section

open Complex Function
p2m_open "UpperHalfPlane~I"
open scoped MatrixGroups ModularForm Manifold

open ModularForm ModularFormClass

namespace W3WsD

variable {N : ℕ} {k : ℤ}

local notation "Γ₀(" N ")" => CongruenceSubgroup.Gamma0 N

theorem hΓ (N : ℕ) : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ₀(N)).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

theorem qCoeff_add (f g : CuspForm Γ₀(N) k) (n : ℕ) :
    qCoeff ⇑(f + g) n = qCoeff ⇑f n + qCoeff ⇑g n := by
  simp only [qCoeff, CuspForm.coe_add]
  rw [ModularForm.qExpansion_add one_pos (hΓ N) f g, map_add]

theorem qCoeff_zero' (n : ℕ) : qCoeff ⇑(0 : CuspForm Γ₀(N) k) n = 0 := by
  simp only [qCoeff, CuspForm.coe_zero]
  rw [UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_zsmul (c : ℤ) (f : CuspForm Γ₀(N) k) (n : ℕ) :
    qCoeff ⇑(c • f) n = c * qCoeff ⇑f n := by
  have h1 : ⇑(c • f) = (c : ℂ) • ⇑f := by
    ext z
    simp
  simp only [qCoeff, h1]
  rw [ModularForm.qExpansion_smul one_pos (hΓ N) (c : ℂ) f]
  simp

def intSubmodule (N : ℕ) (k : ℤ) : Submodule ℤ (CuspForm Γ₀(N) k) where
  carrier := {f | ∀ n : ℕ, ∃ m : ℤ, qCoeff f n = (m : ℂ)}
  add_mem' {f g} hf hg n := by
    obtain ⟨a, ha⟩ := hf n
    obtain ⟨b, hb⟩ := hg n
    exact ⟨a + b, by rw [qCoeff_add, ha, hb]; push_cast; ring⟩
  zero_mem' n := ⟨0, by rw [qCoeff_zero']; simp⟩
  smul_mem' c {f} hf n := by
    obtain ⟨a, ha⟩ := hf n
    exact ⟨c * a, by rw [qCoeff_zsmul, ha]; push_cast; ring⟩

theorem intLattice_eq (N : ℕ) (k : ℤ) : CuspForm.intLattice N k = intSubmodule N k :=
  Submodule.span_eq (intSubmodule N k)

theorem mem_intLattice_iff (f : CuspForm Γ₀(N) k) :
    f ∈ CuspForm.intLattice N k ↔ ∀ n : ℕ, ∃ m : ℤ, qCoeff f n = (m : ℂ) := by
  rw [intLattice_eq]
  rfl

def sturmB (N : ℕ) (k : ℤ) : ℕ := (k * (Γ₀(N)).index).toNat / 12

def trunc (N : ℕ) (k : ℤ) : CuspForm Γ₀(N) k →ₗ[ℤ] (Fin (sturmB N k + 1) → ℂ) where
  toFun f i := qCoeff ⇑f i
  map_add' f g := by
    funext i
    exact qCoeff_add f g i
  map_smul' c f := by
    funext i
    simp only [Pi.smul_apply, eq_intCast, Int.cast_id]
    rw [qCoeff_zsmul, zsmul_eq_mul]

theorem trunc_injective (N : ℕ) [NeZero N] (k : ℤ) : Function.Injective (trunc N k) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_

  have hmf : (ModularFormClass.modularForm f : ModularForm Γ₀(N) k) = 0 := by
    refine ModularForm.sturm_bound_Gamma0 N _ fun n hn ↦ ?_
    have := congrFun hf ⟨n, Nat.lt_succ_of_le hn⟩
    simpa [trunc, qCoeff] using this
  have hcoe : (⇑f : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ModularForm Γ₀(N) k ↦ (⇑F : ℍ → ℂ)) hmf
    simpa using this
  exact DFunLike.coe_injective (hcoe.trans CuspForm.coe_zero.symm)

end W3WsD

open W3WsD in
theorem solution (N : ℕ) [NeZero N] (k : ℤ) : (CuspForm.intLattice N k).FG := by
  classical
  set B := sturmB N k

  set M : Submodule ℤ (Fin (B + 1) → ℂ) :=
    Submodule.span ℤ (Set.range fun i : Fin (B + 1) ↦ (Pi.single i (1 : ℂ) : Fin (B + 1) → ℂ))
    with hM
  have hMfg : M.FG := Submodule.fg_span (Set.finite_range _)

  have hle : (CuspForm.intLattice N k).map (trunc N k) ≤ M := by
    rw [CuspForm.intLattice, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    choose m hm using hf
    have hv : trunc N k f = ∑ i : Fin (B + 1), (m i) • (Pi.single i (1 : ℂ) : Fin (B + 1) → ℂ) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j, Pi.smul_apply, Pi.single_eq_same, zsmul_eq_mul,
        mul_one]
      · exact hm j
      · intro i _ hij
        rw [Pi.smul_apply, Pi.single_eq_of_ne' hij, smul_zero]
      · simp
    rw [hv]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Submodule.fg_of_fg_map_injective (trunc N k) (trunc_injective N k) (hMfg.of_le hle)

end

end S_CuspForm_intLattice_fg
end P2MW
export P2MW.S_CuspForm_intLattice_fg (solution)
