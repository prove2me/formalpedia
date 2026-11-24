-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.isUnit_det_of_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:33.389293+00:00
-- url     : https://prove2.me/submissions/a6140a50-a043-44f1-a4b8-016ea5636ea3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_map_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_isUnit_det_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mk_form_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {e k : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k)
    (X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k)) (hX : Xᴴ * Hq H 𝔭 k * X = Hq H 𝔭 k) : IsUnit X.det := by
  obtain ⟨Y, rfl⟩ := exists_map_mk 𝔭 _ X
  have h1 := isUnit_det_mk hK hFF.out hs hd b hH h𝔭 he hk Y ((mk_form_iff 𝔭 _ H Y).1 hX) k
  have h2 := RingHom.map_det (Ideal.Quotient.mk (extP K 𝔭 ^ k)) Y
  rw [RingHom.mapMatrix_apply] at h2
  rwa [h2] at h1
end Formalism.HermitianLattices.Ext.L3.HU
