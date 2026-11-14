-- Prove2me | solution 1 for ConsistentSubmodular.threeQuarterCertificates
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:41:34.779792+00:00
-- url     : https://prove2.me/submissions/0b6e0830-16ff-4ed9-8282-9b75957778c2

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_WindowCertificates
import Theorems.Thm_ConsistentSubmodular_CompatibleProfile_checkpoint_of_finite_checkpoint
import Theorems.Thm_ConsistentSubmodular_CompatibleProfile_checkpoint_zero_scale
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_root_checkpoint_or_state
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_checkpoint_of_selector_step
import Theorems.Thm_ConsistentSubmodular_AtomicProfile_selector_step
import Theorems.Thm_ConsistentSubmodular_exists_two_labels_of_supportCard

section

noncomputable section

namespace ConsistentSubmodular

variable {m atomCount : ℕ}

/-- Checkpoint certificates are an equivalent form of `FiniteCheckpointGoal`. -/
theorem finiteCheckpointGoal_iff : FiniteCheckpointGoal ↔
    ∀ m atomCount : ℕ, ∀ P : AtomicProfile m atomCount,
      P.Canonical → Nonempty (CheckpointCertificate P) := by
  constructor
  · intro h m a P hP
    obtain ⟨p, en, ex, hs, hsup, hg, he0, he1, hx0, hx1, hes, hxs, hcount⟩ := h m a P hP
    exact ⟨⟨p, en, ex, hs, hsup, hg, he0, he1, hx0, hx1, hes, hxs, hcount⟩⟩
  · intro h m a P hP
    obtain ⟨c⟩ := h m a P hP
    exact ⟨c.point, c.entry, c.exit, c.simplex, c.support, c.stages,
      c.entry_initial, c.entry_terminal, c.exit_initial, c.exit_terminal,
      c.entry_safe, c.exit_safe, c.piece_budget⟩

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace CompatibleProfile

variable {d : ℕ} (P : CompatibleProfile d)

theorem divided_residual (c : ℝ) (hc : 0 < c) (t : ℕ) (i : Fin d) :
    (P.divided c hc).residual t i = P.residual t i / c := by
  exact (sub_div _ _ _).symm

variable {m : ℕ} (Q : CompatibleProfile (m + 1))

theorem divided_multilinearValue (c : ℝ) (hc : 0 < c) (t : ℕ) (p : Point m) :
    (Q.divided c hc).multilinearValue t p = Q.multilinearValue t p / c := by
  unfold multilinearValue finiteExpectation divided Objective.divided
  simp only [div_eq_mul_inv, mul_assoc, Finset.sum_mul]

theorem divided_path_transfer (c : ℝ) (hc : 0 < c) (t : ℕ) (a : ℝ) (γ : PolygonalPath m)
    (h : (Q.divided c hc).SafePath t (a / c) γ) : Q.SafePath t a γ := by
  constructor
  · intro j
    have hj := h.1 j
    rw [Q.divided_multilinearValue] at hj
    exact ⟨hj.1, (div_le_div_iff_of_pos_right hc).mp hj.2⟩
  · intro j x hx hx'
    have hj := h.2 j x hx hx'
    rw [Q.divided_multilinearValue] at hj
    exact ⟨hj.1, (div_le_div_iff_of_pos_right hc).mp hj.2⟩

theorem checkpoint_positive_scale_of_finite_checkpoint
    (hfinite : FiniteCheckpointGoal) (hscale : 0 < Q.residual 0 0)
    (hopt : ∀ t : Fin (m + 1), ∀ i, Q.residual t.val i ≤ Q.residual t.val t) :
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t : Fin (m + 1), (3 : ℝ) / 4 * (Q.objective t.val).value {t} ≤ Q.multilinearValue t.val p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      Q.SafePath 0 ((3 : ℝ) / 4 * (Q.objective 0).value {0}) entry ∧
      Q.SafePath m ((3 : ℝ) / 4 * (Q.objective m).value {Fin.last m}) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2 := by
  let c := Q.residual 0 0
  have hinit : (Q.divided c hscale).residual 0 0 = 1 := by
    rw [Q.divided_residual]
    exact div_self (ne_of_gt hscale)
  have hopt' : ∀ t : Fin (m + 1), ∀ i,
      (Q.divided c hscale).residual t.val i ≤ (Q.divided c hscale).residual t.val t := by
    intro t i
    rw [Q.divided_residual, Q.divided_residual]
    exact (div_le_div_iff_of_pos_right hscale).mpr (hopt t i)
  obtain ⟨p, entry, exit, hp, hsupp, hstage, he0, he1, hx0, hx1, hentry, hexit, hpieces⟩ :=
    (Q.divided c hscale).checkpoint_of_finite_checkpoint hinit hopt' hfinite
  refine ⟨p, entry, exit, hp, hsupp, ?_, he0, he1, hx0, hx1, ?_, ?_, hpieces⟩
  · intro t
    have ht := hstage t
    rw [Q.divided_multilinearValue] at ht
    change (3 : ℝ) / 4 * ((Q.objective t.val).value {t} / c) ≤ Q.multilinearValue t.val p / c at ht
    rw [← mul_div_assoc] at ht
    exact (div_le_div_iff_of_pos_right hscale).mp ht
  · apply Q.divided_path_transfer c hscale
    simpa only [divided, Objective.divided, mul_div_assoc] using hentry
  · apply Q.divided_path_transfer c hscale
    simpa only [divided, Objective.divided, mul_div_assoc] using hexit

/-- Full compatible-profile reduction, including zero initial scale and
arbitrary nonnegative initial baseline. -/
theorem checkpoint_for_compatible (hfinite : FiniteCheckpointGoal)
    (hopt : ∀ t : Fin (m + 1), ∀ i, Q.residual t.val i ≤ Q.residual t.val t) :
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t : Fin (m + 1), (3 : ℝ) / 4 * (Q.objective t.val).value {t} ≤ Q.multilinearValue t.val p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      Q.SafePath 0 ((3 : ℝ) / 4 * (Q.objective 0).value {0}) entry ∧
      Q.SafePath m ((3 : ℝ) / 4 * (Q.objective m).value {Fin.last m}) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2 := by
  by_cases hzero : Q.residual 0 0 = 0
  · exact Q.checkpoint_zero_scale hzero (hopt 0)
  · have hpos : 0 < Q.residual 0 0 :=
      lt_of_le_of_ne (Q.residualOn_nonnegative 0 {0}) (Ne.symm hzero)
    exact Q.checkpoint_positive_scale_of_finite_checkpoint hfinite hpos hopt

end CompatibleProfile

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ}

theorem suffix_strict (P : AtomicProfile m atomCount) (hP : P.Canonical)
    (h : Fin (m + 1)) (hlast : ∀ i, h < i → P.designated i ≠ 1)
    (t : Fin (m - h.val + 1)) (ht : 0 < t) : (P.suffix h).designated t < 1 := by
  rw [P.suffix_designated]
  apply lt_of_le_of_ne (P.designated_le_one hP _)
  apply hlast
  change h.val < h.val + t.val
  have : 0 < t.val := ht
  omega

theorem exists_last_unit (P : AtomicProfile m atomCount) (hP : P.Canonical) :
    ∃ h : Fin (m + 1), P.designated h = 1 ∧ ∀ i, h < i → P.designated i ≠ 1 := by
  let units := univ.filter (fun i => P.designated i = 1)
  have hn : units.Nonempty := ⟨0, mem_filter.mpr ⟨mem_univ _, hP.1⟩⟩
  let h := units.max' hn
  refine ⟨h, (mem_filter.mp (max'_mem units hn)).2, ?_⟩
  intro i hi heq
  have hmem : i ∈ units := mem_filter.mpr ⟨mem_univ _, heq⟩
  have hle : i ≤ h := le_max' units i hmem
  exact (not_le.mpr hi) hle

end AtomicProfile

/-- It suffices to solve the normalized case whose designated residual is
strictly below one at every positive stage. This reduction includes the deletion
of empty incidences and the complete path piece budget. -/
theorem finiteCheckpoint_of_strict
    (strict : ∀ m a : ℕ, ∀ P : AtomicProfile m a, P.Canonical →
      (∀ t : Fin (m + 1), 0 < t → P.designated t < 1) →
      Nonempty (CheckpointCertificate P)) : FiniteCheckpointGoal := by
  rw [finiteCheckpointGoal_iff]
  intro m a P hP
  obtain ⟨h, hh, hlast⟩ := P.exists_last_unit hP
  obtain ⟨c⟩ := strict (m - h.val) a (P.suffix h) (P.suffix_canonical hP h hh)
    (P.suffix_strict hP h hlast)
  exact ⟨P.liftSuffixCheckpoint hP h hh c⟩

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem finite_checkpoint_strict (hP : P.Canonical)
    (hstrict : ∀ t : Fin (m + 1), 0 < t → P.designated t < 1) :
    Nonempty (CheckpointCertificate P) := by
  rcases P.root_checkpoint_or_state hP hstrict with hyes | ⟨h, ⟨S⟩⟩
  · exact hyes
  · exact P.checkpoint_of_selector_step (P.selector_step hP) h S

end AtomicProfile

/-- The finite checkpoint theorem, including all stages, both prescribed path
endpoints, every segment and node, and the `d + 2` piece budget. -/
theorem finiteCheckpoint : FiniteCheckpointGoal :=
  finiteCheckpoint_of_strict (fun _ _ P hP hstrict => P.finite_checkpoint_strict hP hstrict)

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

theorem profile_optimal (t i : Fin (W.lastStage + 1)) :
    W.profile.residual t.val i ≤ W.profile.residual t.val t := by
  simp only [CompatibleProfile.residual, CompatibleProfile.residualOn,
    CompatibleProfile.baseline, profile, CompatibleProfile.fromPhysical,
    Objective.onTypes_singleton, Objective.onTypes_empty, arrivalsAt_stage]
  have h := W.candidate_optimal t (W.candidate i) (W.candidate_subset i) (W.candidate_card i)
  rw [Finset.union_comm (W.candidate i), Finset.union_comm (W.candidate t)] at h
  linarith

/-- The finite checkpoint theorem applied to the window's profile gives a
`(3/4, m + 3)`-certificate whose anchor is supported on at most two
candidates. -/
theorem exists_twoLabelCertificate :
    ∃ Z : W.Certificate (3 / 4) (W.lastStage + 3),
      ∃ a b : Fin (W.lastStage + 1), ∀ i, i ≠ a → i ≠ b → Z.anchor i = 0 := by
  obtain ⟨p, entry, exit, hp, hsupp, hstage, he0, he1, hx0, hx1, hentry, hexit, hpieces⟩ :=
    W.profile.checkpoint_for_compatible finiteCheckpoint W.profile_optimal
  exact ⟨W.certificateOfProfile p entry exit hp hstage he0 he1 hx0 hx1 hentry hexit
    (by omega), exists_two_labels_of_supportCard hsupp⟩

/-- Theorem 7 for one window. -/
theorem exists_threeQuarterCertificate :
    Nonempty (W.Certificate (3 / 4) (W.lastStage + 3)) :=
  let ⟨Z, _⟩ := W.exists_twoLabelCertificate
  ⟨Z⟩

end WindowInstance

namespace Certificates

/-- Theorem 7: every window admits a `(3/4, m + 3)`-certificate. -/
theorem threeQuarterCertificates : ThreeQuarterCertificatesGoal :=
  fun _ W => W.exists_threeQuarterCertificate

end Certificates

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution : ThreeQuarterCertificatesGoal :=
  Certificates.threeQuarterCertificates

end
