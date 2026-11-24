-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_weyl_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:18.505346+00:00
-- url     : https://prove2.me/submissions/eded7a93-652a-43de-ae66-a3e524475ba9

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Theorems.Thm_Formalism_L2_G_Model_sw_bidet_map
import Theorems.Thm_Formalism_L2_G_Model_sw_weyl_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylRational


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model
theorem _root_.solution (K : Type) [Field K] [CharZero K] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    weyl K r n hn ν = dualWeyl K r n ν := by
  apply le_antisymm (weylLeDual K r n hn ν hν)
  obtain ⟨b, hb, h2⟩ := sSBasis K r n ν
  rw [← hb.2.1, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨-, -, N, sz, hsz, I, hshape, -, hbm⟩ := h2 i
  have h3 : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ r n ν := by
    have := bidetMem ℤ r n N sz hsz I
    rwa [hshape] at this
  obtain ⟨c, hc, h4⟩ := weylRational r n hn ν hν _ h3
  have h5 := sw_weyl_map (Int.castRingHom K) hn ν _ h4
  rw [zsmul_eq_mul, map_mul, map_intCast, sw_bidet_map, ← hbm] at h5
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc
  have h6 : b i = (c : K)⁻¹ • (((c : ℤ) : MvPolynomial (Fin r × Fin n) K) * b i) := by
    rw [smul_eq_C_mul, ← mul_assoc]
    have : (C (c : K)⁻¹ : MvPolynomial (Fin r × Fin n) K) * ((c : ℤ) : MvPolynomial (Fin r × Fin n) K) = 1 := by
      rw [← map_intCast (C : K →+* MvPolynomial (Fin r × Fin n) K), ← map_mul, inv_mul_cancel₀ hcK, map_one]
    rw [this, one_mul]
  show b i ∈ weyl K r n hn ν
  rw [h6]
  exact Submodule.smul_mem _ _ h5
end Formalism.L2.G.Model
