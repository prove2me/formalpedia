-- Prove2me | solution 1 for Formalism.L2.Ker.KS.exists_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:40:13.288851+00:00
-- url     : https://prove2.me/submissions/f4689964-732a-4770-abca-a4c85462eee3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
import Theorems.Thm_Formalism_L2_Ker_KS_lattice_ext
import Theorems.Thm_Formalism_L2_Ker_KS_form_core
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Ker.KS
open Formalism.L2.Th1.H (cmL CmOK)
section Pt
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
end Pt
private theorem exists_cmL_lattice_eq_of_cm_action (d : ℕ) (hd : 0 < d) (L : PeriodPair) (w1 w2 : ℂ) (hw1 : w1 ≠ 0)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) * w1 + (n : ℂ) * w2 = z)
    (p q r s : ℤ) (hq : 0 < q)
    (h1 : (p : ℂ) * w1 + (q : ℂ) * w2 = Formalism.L2.Th1.F.cmTheta 1 d * w1)
    (h2 : (r : ℂ) * w1 + (s : ℂ) * w2 = Formalism.L2.Th1.F.cmTheta 1 d * w2) :
    ∃ (a : ℕ) (b c : ℤ) (ha : 0 < a) (lam : ℂ) (hlam : lam ≠ 0), 4 * (a : ℤ) * c = b ^ 2 + d ∧
      (cmL a b d ha hd lam hlam).lattice = L.lattice := by
  obtain ⟨hf, hne, he1, he2⟩ := form_core d hd w1 w2 hw1 p q r s hq h1 h2
  have hqz : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq.le
  have hqt : ((q.toNat : ℕ) : ℂ) = (q : ℂ) := by
    have e : (((q.toNat : ℕ) : ℤ) : ℂ) = ((q : ℤ) : ℂ) := by rw [hqz]
    push_cast at e
    exact e
  refine ⟨q.toNat, 1 - 2 * p, -r, by omega, w1 / q, hne, ?_, ?_⟩
  · rw [hqz]
    linear_combination hf
  · apply lattice_ext
    intro z
    rw [PeriodPair.mem_lattice, hL]
    have e1 : (cmL q.toNat (1 - 2 * p) d (by omega) hd (w1 / q) hne).ω₁ = w1 := by
      show w1 / q * ((q.toNat : ℕ) : ℂ) = w1
      rw [hqt]
      exact he1.symm
    have e2 : (cmL q.toNat (1 - 2 * p) d (by omega) hd (w1 / q) hne).ω₂ = w2 := he2.symm
    rw [e1, e2]
end Formalism.L2.Ker.KS
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Ker Formalism.L2.Ker.KS
open Formalism.L2.Th1.H (cmL CmOK)
namespace Formalism.L2.Ker.KS
theorem _root_.solution (d : ℕ) (hd : 0 < d) (L : PeriodPair) (hst : ∀ x ∈ L.lattice, Formalism.L2.Th1.F.cmTheta 1 d * x ∈ L.lattice) :
    ∃ (a : ℕ) (b c : ℤ) (ha : 0 < a) (lam : ℂ) (hlam : lam ≠ 0), 4 * (a : ℤ) * c = b ^ 2 + d ∧
      (cmL a b d ha hd lam hlam).lattice = L.lattice := by
  have hw1 : L.ω₁ ≠ 0 := by
    intro h0
    have hind := L.indep
    rw [LinearIndependent.pair_iff] at hind
    have := (hind 1 0 (by rw [h0]; simp)).1
    norm_num at this
  obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp (hst _ L.ω₁_mem_lattice)
  obtain ⟨r, s, hrs⟩ := PeriodPair.mem_lattice.mp (hst _ L.ω₂_mem_lattice)
  have hq0 : q ≠ 0 := by
    rintro rfl
    have hθ : Formalism.L2.Th1.F.cmTheta 1 d = (p : ℂ) := by
      have e : (Formalism.L2.Th1.F.cmTheta 1 d - p) * L.ω₁ = 0 := by
        push_cast at hpq
        linear_combination -hpq
      have e' := (mul_eq_zero.mp e).resolve_right hw1
      linear_combination e'
    have hind := (Formalism.L2.Th1.F.cmPair 1 1 d one_pos hd).indep
    rw [LinearIndependent.pair_iff] at hind
    have := (hind (p : ℝ) (-1) (by
      show (p : ℝ) • (((1 : ℕ) : ℂ)) + (-1 : ℝ) • Formalism.L2.Th1.F.cmTheta 1 d = 0
      rw [hθ, Complex.real_smul, Complex.real_smul]
      push_cast
      ring)).2
    norm_num at this
  rcases lt_or_gt_of_ne hq0 with hneg | hpos
  · refine exists_cmL_lattice_eq_of_cm_action d hd L L.ω₁ (-L.ω₂) hw1 (fun z => ?_) p (-q) (-r) s (by omega)
      (by push_cast; linear_combination hpq) (by push_cast; linear_combination -hrs)
    rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, h⟩
      exact ⟨m, -n, by push_cast; rw [← h]; ring⟩
    · rintro ⟨m, n, h⟩
      exact ⟨m, -n, by push_cast; rw [← h]; ring⟩
  · exact exists_cmL_lattice_eq_of_cm_action d hd L L.ω₁ L.ω₂ hw1 (fun z => PeriodPair.mem_lattice) p q r s hpos hpq hrs
end Formalism.L2.Ker.KS
