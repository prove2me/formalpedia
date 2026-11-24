-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.qp_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:10.929697+00:00
-- url     : https://prove2.me/submissions/fbb800b0-41fe-44a2-b327-53b0ce8507b2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_qp_of_half_notMem
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_qp_two_mul
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_semiChar_sq
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_coords_half
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.F
namespace PeriodLatticeBasisLemmas
private theorem mem_lattice_iff_exists_int_comb' (L : PeriodPair) {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ = x := by
  exact L.mem_lattice
private theorem int_comb_periods_mem_lattice (L : PeriodPair) (a b : ℤ) :
    (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ ∈ L.lattice :=
  (mem_lattice_iff_exists_int_comb' L).mpr ⟨a, b, rfl⟩
private theorem semiChar_zero_eq_one (L : PeriodPair) : Formalism.L2.Th1.F.semiChar L 0 = 1 := by
  unfold Formalism.L2.Th1.F.semiChar
  rw [if_pos (by rw [zero_div]; exact L.lattice.zero_mem)]
private theorem quasiPeriodic_zero_semiChar_zero (L : PeriodPair) : QP L 0 (Formalism.L2.Th1.F.semiChar L 0) := by
  rw [semiChar_zero_eq_one]
  unfold QP
  intro z
  simp
end PeriodLatticeBasisLemmas
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
namespace Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
theorem _root_.solution (hq : ZetaQuasi) (hl : SigmaLogDeriv) (ho : SigmaOdd) (hz : SigmaZero)
    (L : PeriodPair) : ∀ n : ℕ, ∀ a b : ℤ, a.natAbs + b.natAbs ≤ n →
      QP L (a * L.ω₁ + b * L.ω₂) (semiChar L (a * L.ω₁ + b * L.ω₂)) := by
  intro n
  induction n with
  | zero =>
    intro a b h
    have ha : a = 0 := Int.natAbs_eq_zero.mp (by omega)
    have hb : b = 0 := Int.natAbs_eq_zero.mp (by omega)
    subst ha hb
    have e : ((0 : ℤ) : ℂ) * L.ω₁ + ((0 : ℤ) : ℂ) * L.ω₂ = 0 := by simp
    rw [e]
    exact quasiPeriodic_zero_semiChar_zero L
  | succ n ih =>
    intro a b h
    by_cases h2 : ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) / 2 ∈ L.lattice
    · obtain ⟨a', b', hab⟩ := (mem_lattice_iff_exists_int_comb' L).mp h2
      obtain ⟨rfl, rfl⟩ := coords_half L hab
      have e2 : (2 : ℤ).natAbs = 2 := rfl
      rw [Int.natAbs_mul, Int.natAbs_mul, e2] at h
      have ih' := ih a' b' (by omega)
      have h3 := qp_two_mul L ih' (semiChar_sq L _)
      have hs1 : Formalism.L2.Th1.F.semiChar L (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂) = 1 := by
        unfold Formalism.L2.Th1.F.semiChar
        rw [if_pos h2]
      rw [hs1, show (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂)
          = 2 * ((a' : ℂ) * L.ω₁ + (b' : ℂ) * L.ω₂) by push_cast; ring]
      exact h3
    · have hs1 : Formalism.L2.Th1.F.semiChar L ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) = -1 := by
        unfold Formalism.L2.Th1.F.semiChar
        rw [if_neg h2]
      rw [hs1]
      exact qp_of_half_notMem hq hl ho hz L (int_comb_periods_mem_lattice L a b) h2
end Formalism.L2.Th1.F.PeriodLatticeBasisLemmas
