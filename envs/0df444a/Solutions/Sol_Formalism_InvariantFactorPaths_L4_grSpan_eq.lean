-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.grSpan_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:38:59.427935+00:00
-- url     : https://prove2.me/submissions/3c24c8f2-0fd3-4e03-b0e6-97bcb26c90ea

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_p_pow_ne_zero
import Theorems.Thm_Formalism_GM_TM_exists_pow_smul_intPol
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_graded_eq_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_initPart_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restriction_min_max_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e e1 : ℕ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true)
    (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hO : ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    x ∈ grSpan p LLw J M ρ w e ↔
      ∃ y ∈ XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        x = X (Fin.last K, ρ) ^ e * y := by
  have hMM := restriction_min_max_holds p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) e1
    hr hρ hv hP hE hO
  have hGr := graded_eq_holds p K r LLw J M ρ w e hv he
  constructor
  · intro hx
    have hle : grSpan p LLw J M ρ w e ≤
        (XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e)).map
          (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) := by
      unfold grSpan
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨h, hh, rfl⟩ := (hGr z).mp hz
      refine Submodule.mem_map.mpr ⟨initPart (Fin.last K, ρ) 0 h, (hMM _).mpr ⟨h, ?_, rfl⟩, rfl⟩
      exact (Submodule.mem_inf.mp hh).1
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hle hx)
    exact ⟨y, hy, hyx.symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := (hMM y).mp hy
    obtain ⟨n, hn⟩ := exists_pow_smul_intPol h
    have h1 : ((p : ℚ_[p]) ^ n) • h ∈
        MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) :=
      Submodule.mem_inf.mpr ⟨Submodule.smul_mem _ _ hh, hn⟩
    have h2 : X (Fin.last K, ρ) ^ e * initPart (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ n) • h) ∈
        grSpan p LLw J M ρ w e := Submodule.subset_span ((hGr _).mpr ⟨_, h1, rfl⟩)
    have h3 := (grSpan p LLw J M ρ w e).smul_mem (((p : ℚ_[p]) ^ n)⁻¹) h2
    rwa [initPart_smul, mul_smul_comm, smul_smul, inv_mul_cancel₀ (p_pow_ne_zero n), one_smul] at h3
end Formalism.InvariantFactorPaths.L4
