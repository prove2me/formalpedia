-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.covol_eq_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:21.849012+00:00
-- url     : https://prove2.me/submissions/01820657-1168-4a53-9683-3b4d7d8f9fd0

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Theorems.Thm_Formalism_HN_QuotientRealization_transport_apply
import Theorems.Thm_Formalism_F_covolEqGram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.QuotientRealization
variable {E F M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [AddCommGroup M]
namespace Formalism.HN.QuotientRealization
theorem _root_.solution (f : M →+ E) (g : M →+ F) (L1 : Submodule ℤ E) (L2 : Submodule ℤ F)
    [DiscreteTopology L1] [DiscreteTopology L2]
    (h1 : ∀ y, y ∈ L1 ↔ ∃ m, f m = y) (h2 : ∀ y, y ∈ L2 ↔ ∃ m, g m = y)
    (hn : ∀ m, ‖f m‖ = ‖g m‖) : Formalism.F.covol L1 = Formalism.F.covol L2 := by
  have hn' : ∀ m, ‖g m‖ = ‖f m‖ := fun m => (hn m).symm
  let φ := transport f g L1 L2 h1 h2 hn
  let ψ := transport g f L2 L1 h2 h1 hn'
  let e : L1 ≃+ L2 :=
    { toFun := φ
      invFun := ψ
      map_add' := φ.map_add
      left_inv := fun y => by
        obtain ⟨m, hm⟩ := (h1 _).1 y.2
        apply Subtype.ext
        rw [transport_apply g f L2 L1 h2 h1 hn' (φ y) m
          (transport_apply f g L1 L2 h1 h2 hn y m hm).symm, hm]
      right_inv := fun y => by
        obtain ⟨m, hm⟩ := (h2 _).1 y.2
        apply Subtype.ext
        rw [transport_apply f g L1 L2 h1 h2 hn (ψ y) m
          (transport_apply g f L2 L1 h2 h1 hn' y m hm).symm, hm] }
  let bL := Module.finBasis ℤ L1
  rw [Formalism.F.covolEqGram E L1 _ bL, Formalism.F.covolEqGram F L2 _ (bL.map e.toIntLinearEquiv)]
  congr 2
  ext i j
  obtain ⟨mi, hmi⟩ := (h1 _).1 (bL i).2
  obtain ⟨mj, hmj⟩ := (h1 _).1 (bL j).2
  have hi : ((bL.map e.toIntLinearEquiv) i : F) = g mi := by
    rw [Basis.map_apply]; exact transport_apply f g L1 L2 h1 h2 hn _ mi hmi
  have hj : ((bL.map e.toIntLinearEquiv) j : F) = g mj := by
    rw [Basis.map_apply]; exact transport_apply f g L1 L2 h1 h2 hn _ mj hmj
  simp only [Matrix.gram_apply]
  rw [hi, hj, ← hmi, ← hmj, real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add, ← map_add,
    hn, hn, hn]
end Formalism.HN.QuotientRealization
