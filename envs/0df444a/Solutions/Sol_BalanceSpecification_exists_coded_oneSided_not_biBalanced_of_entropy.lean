-- Prove2me | solution 1 for BalanceSpecification.exists_coded_oneSided_not_biBalanced_of_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:28.420809+00:00
-- url     : https://prove2.me/submissions/c2df4e87-b1c0-473c-aa70-b0c566f6e505

module
public import Definitions.Def_BalanceSpecificaton_MarkerConstruction
public import Definitions.Def_BalanceSpecificaton_EntropyModel
public import Definitions.Def_BalanceSpecificaton_ArbitraryEntropy
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_entropy_renamedShift
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_hasSpecification_renamedShift
public import Theorems.Thm_BalanceSpecification_exists_oneSided_marker_extension
public import Theorems.Thm_BalanceSpecification_exists_specification_shift_of_entropy


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {h : ℝ} (hh : 0 < h) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ X : ShiftSpace (ArbitraryEntropy.Alphabet n),
      ∃ hX : X.carrier.Nonempty,
        IsCoded X ∧ entropy X hX = h ∧
        (RightBalanced (language X) ∨ LeftBalanced (language X)) ∧
        ¬BiBalanced (language X) ∧ ¬HasVariableSpecification X ∧
        ∃ Y : ShiftSpace (ArbitraryEntropy.Alphabet n), ∃ hY : Y.carrier.Nonempty,
          Y.carrier ⊆ X.carrier ∧ HasSpecification Y ∧ entropy Y hY = h := by
  obtain ⟨n, hn, Y, hY, hspec, hentropy⟩ := exists_specification_shift_of_entropy hh.le
  have hpos : 0 < entropy Y hY := by rw [hentropy]; exact hh
  obtain ⟨X, hX, hcode, _, hXentropy, hright, hnotleft, hnotvar, hsub⟩ :=
    exists_oneSided_marker_extension hY hspec hpos
  let Z := MarkerEmbedding.renamedShift (some : (Fin n × Bool) → ArbitraryEntropy.Alphabet n) Y
  have hZ : Z.carrier.Nonempty := MarkerEmbedding.renamedShift_nonempty _ hY
  have hZentropy : entropy Z hZ = h :=
    (MarkerEmbedding.entropy_renamedShift (Option.some_injective _) hY).trans hentropy
  refine ⟨n, hn, X, hX, hcode, hXentropy.trans hentropy, Or.inl hright,
    (fun hbial => hnotleft hbial.2), hnotvar, Z, hZ, hsub, ?_, hZentropy⟩
  exact MarkerEmbedding.hasSpecification_renamedShift _ hspec
end BalanceSpecification
