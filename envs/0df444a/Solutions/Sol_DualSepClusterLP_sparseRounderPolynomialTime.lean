-- Prove2me | solution 1 for DualSepClusterLP.sparseRounderPolynomialTime
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T13:42:03.772444+00:00
-- url     : https://prove2.me/submissions/88484443-4c79-47f2-bb87-c2cadde62fea

import Mathlib
import Definitions.Def_DualSepClusterLP_SparseRounder

/-
Finite-alphabet polynomial-time machine combinators from openai/math (Apache-2.0),
commit 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. The source below incorporates
Lean 4.33.1 compatibility edits to conditional rewrite lemmas.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

/- OAI.Combinatorics.KMedian.Model -/
section
namespace OAI




section
section
namespace MetricKMedian

structure Instance where
  n : ℕ
  distance : Fin n → Fin n → ℚ
  clients : Finset (Fin n)
  facilities : Finset (Fin n)
  k : ℕ
  distance_nonneg : ∀ i j, 0 ≤ distance i j
  distance_eq_zero : ∀ i j, distance i j = 0 ↔ i = j
  distance_symm : ∀ i j, distance i j = distance j i
  distance_triangle : ∀ i j h, distance i h ≤ distance i j + distance j h
  k_pos : 1 ≤ k
  k_le : k ≤ facilities.card

def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeRat (q : ℚ) : List Bool :=
  [decide (q.num < 0)] ++ encodeNat q.num.natAbs ++ encodeNat q.den

def encodeInstance (I : Instance) : List Bool :=
  encodeNat I.n ++ encodeNat I.k ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.n =>
      (List.ofFn (fun j : Fin I.n => encodeRat (I.distance i j))).flatten)).flatten

noncomputable def nearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) : ℝ :=
  if h : S.Nonempty then
    (S.image (fun i => (I.distance j i : ℝ))).min' (h.image _)
  else 0

noncomputable def cost (I : Instance) (S : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ I.clients, nearest I j S

def feasibleSets (I : Instance) : Finset (Finset (Fin I.n)) :=
  I.facilities.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ I.k)

noncomputable def optimum (I : Instance) : ℝ :=
  if h : (feasibleSets I).Nonempty then
    ((feasibleSets I).image (cost I)).min' (h.image _)
  else 0

def Correct (epsilon : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧
    cost I S ≤ (1 + 2 / Real.exp 1 + epsilon) * optimum I


end MetricKMedian
end
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanMachine -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Turing StateTransition Function Finset

structure Machine where
  K : Type
  [decK : DecidableEq K]
  [finK : Fintype K]
  input : K
  output : K
  Label : Type
  [finLabel : Fintype Label]
  main : Label
  State : Type
  [finState : Fintype State]
  initial : State
  code : Label → TM2.Stmt (fun _ : K => Bool) Label State

attribute [instance] Machine.decK Machine.finK Machine.finLabel Machine.finState

namespace Machine

def tm (M : Machine) : FinTM2 where
  K := M.K
  k₀ := M.input
  k₁ := M.output
  Γ _ := Bool
  Λ := M.Label
  main := M.main
  σ := M.State
  initialState := M.initial
  m := M.code

instance allWorkFinite (M : Machine) (k : M.tm.K) : Fintype (M.tm.Γ k) :=
  inferInstanceAs (Fintype Bool)

abbrev Cfg (M : Machine) := TM2.Cfg (fun _ : M.K => Bool) M.Label M.State

def initialCfg (M : Machine) (s : List Bool) : M.Cfg :=
  ⟨some M.main, M.initial, fun k => if k=M.input then s else []⟩

def finalCfg (M : Machine) (s : List Bool) : M.Cfg :=
  ⟨none, M.initial, fun k => if k=M.output then s else []⟩

@[simp] theorem init_eq (M : Machine) (s : List Bool) :
    initList M.tm s=M.initialCfg s := by
  rfl

@[simp] theorem halt_eq (M : Machine) (s : List Bool) :
    haltList M.tm s=M.finalCfg s := by
  rfl

abbrev step (M : Machine) : M.Cfg → Option M.Cfg := TM2.step M.code

end Machine

theorem cfg_ext {K L S : Type} {a b : TM2.Cfg (fun _ : K => Bool) L S}
    (hl : a.l=b.l) (hv : a.var=b.var) (hs : a.stk=b.stk) : a=b := by
  cases a
  cases b
  cases hl
  cases hv
  cases hs
  rfl

inductive Trace {α : Type*} (f : α → Option α) : ℕ → α → α → Prop
  | refl (a : α) : Trace f 0 a a
  | cons {n : ℕ} {a b c : α} : f a=some b → Trace f n b c → Trace f (n+1) a c

namespace Trace
variable {α β : Type*} {f : α → Option α}

theorem trans {n m : ℕ} {a b c : α} (h : Trace f n a b) (g : Trace f m b c) :
    Trace f (n+m) a c := by
  induction h with
  | refl => simpa using g
  | cons hs ht ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cons hs (ih g)

theorem map {g : β → Option β} (e : α → β)
    (he : ∀ a b, f a=some b → g (e a)=some (e b))
    {n : ℕ} {a b : α} (h : Trace f n a b) : Trace g n (e a) (e b) := by
  induction h with
  | refl => exact refl _
  | cons hs _ ih => exact cons (he _ _ hs) ih

theorem iterate_eq {n : ℕ} {a b : α} (h : Trace f n a b) :
    (flip bind f)^[n] (some a)=some b := by
  induction h with
  | refl => rfl
  | cons hs ht ih =>
      rw [Function.iterate_succ_apply,show (flip bind f) (some _)=_ from hs]
      exact ih

theorem of_iterate {n : ℕ} {a b : α}
    (h : (flip bind f)^[n] (some a)=some b) : Trace f n a b := by
  induction n generalizing a with
  | zero =>
      have hab : a=b := Option.some.inj h
      subst b
      exact refl a
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      cases hc : f a with
      | none =>
          have hz : ∀ t : ℕ, (flip bind f)^[t] (none : Option α)=none := by
            intro t
            induction t with
            | zero => rfl
            | succ t iht =>
                rw [Function.iterate_succ_apply]
                exact iht
          change (flip bind f)^[n] (f a)=some b at h
          rw [hc,hz] at h
          contradiction
      | some c =>
          have hh : (flip bind f)^[n] (some c)=some b := by
            change (flip bind f)^[n] (f a)=some b at h
            rwa [hc] at h
          exact cons hc (ih hh)

def inTime {n : ℕ} {a b : α} (h : Trace f n a b) :
    EvalsToInTime f a (some b) n := ⟨⟨n,h.iterate_eq⟩,le_rfl⟩

theorem of_inTime {n : ℕ} {a b : α} (h : EvalsToInTime f a (some b) n) :
    Trace f h.steps a b := of_iterate h.evals_in_steps

end Trace

namespace Machine
variable {K L S : Type} [DecidableEq K]

def pushes : TM2.Stmt (fun _ : K => Bool) L S → ℕ
  | .push _ _ q => 1+pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

def volume [Fintype K] (s : K → List Bool) : ℕ := ∑ k, (s k).length

variable [Fintype K]

theorem volume_update (s : K → List Bool) (k : K) (v : List Bool) :
    volume (update s k v)+(s k).length=volume s+v.length := by
  classical
  unfold volume
  have he : (fun j => (update s k v j).length)=update (fun j => (s j).length) k v.length := by
    funext j
    simp only [update_apply]
    split <;> rfl
  rw [he,Finset.sum_update_of_mem (mem_univ k)]
  have hh := Finset.sum_erase_add (univ : Finset K) (fun j => (s j).length) (mem_univ k)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : TM2.Stmt (fun _ : K => Bool) L S)
    (v : S) (s : K → List Bool) :
    volume (TM2.stepAux q v s).stk ≤ volume s+pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have h := ih v (update s k (g v::s k))
      have hv := volume_update s k (g v::s k)
      simp only [List.length_cons] at hv
      simpa only [TM2.stepAux,pushes,Nat.add_assoc] using (by omega :
        volume (TM2.stepAux q v (update s k (g v::s k))).stk≤volume s+(1+pushes q))
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have h := ih (g v (s k).head?) (update s k (s k).tail)
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      simp only [TM2.stepAux,pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simpa only [TM2.stepAux,hg,Bool.false_eq_true,Bool.cond_false,pushes] using
          (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simpa only [TM2.stepAux,hg,Bool.cond_true,pushes] using
          (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]
  | halt => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]

def growth (M : Machine) : ℕ := ∑ l, pushes (M.code l)

theorem step_volume (M : Machine) (a b : M.Cfg) (h : M.step a=some b) :
    volume b.stk ≤ volume a.stk+M.growth := by
  rcases a with ⟨l,v,s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b=TM2.stepAux (M.code l) v s := (Option.some.inj h).symm
      rw [hb]
      exact (stepAux_volume _ _ _).trans (Nat.add_le_add_left
        (show pushes (M.code l) ≤ M.growth from
          single_le_sum (f:=fun x => pushes (M.code x)) (fun _ _ => Nat.zero_le _) (mem_univ l)) _)

theorem trace_volume (M : Machine) {n : ℕ} {a b : M.Cfg}
    (h : Trace M.step n a b) : volume b.stk ≤ volume a.stk+n*M.growth := by
  induction h with
  | refl => simp
  | @cons n a b c hab hbc ih =>
      have hs := M.step_volume a b hab
      calc
        _ ≤ volume b.stk+n*M.growth := ih
        _ ≤ volume a.stk+(n+1)*M.growth := by rw [Nat.add_mul]; omega

@[simp] theorem initial_volume (M : Machine) (s : List Bool) :
    volume (M.initialCfg s).stk=s.length := by
  classical
  simp only [initialCfg,volume,apply_ite List.length,List.length_nil]
  simp

@[simp] theorem final_volume (M : Machine) (s : List Bool) :
    volume (M.finalCfg s).stk=s.length := by
  classical
  simp only [finalCfg,volume,apply_ite List.length,List.length_nil]
  simp

theorem output_length (M : Machine) {s t : List Bool} {n : ℕ}
    (h : TM2OutputsInTime M.tm s (some t) n) : t.length ≤ s.length+n*M.growth := by
  have ht : Trace M.step h.steps (M.initialCfg s) (M.finalCfg t) :=
    Trace.of_iterate h.evals_in_steps
  have hv := M.trace_volume ht
  simp only [initial_volume,final_volume] at hv
  exact hv.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Machine
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanEmbedding -/
section
namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Turing Function

structure Embedding (K L S K' L' S' : Type) [DecidableEq K] [DecidableEq K'] where
  key : K → K'
  read : S' → S
  write : S' → S → S'
  state : S → S'
  read_state : ∀ v, read (state v)=v
  write_state : ∀ v w, write (state v) w=state w
  stack : (K → List Bool) → K' → List Bool
  stack_key : ∀ s k, stack s (key k)=s k
  stack_update : ∀ s k x, stack (update s k x)=update (stack s) (key k) x
  label : L → L'
  halted : Option L'
  stop : TM2.Stmt (fun _ : K' => Bool) L' S'
  stop_spec : ∀ v s, TM2.stepAux stop (state v) (stack s)=⟨halted,state v,stack s⟩

namespace Embedding
variable {K L S K' L' S' : Type} [DecidableEq K] [DecidableEq K']
variable (E : Embedding K L S K' L' S')

def stmt : TM2.Stmt (fun _ : K => Bool) L S → TM2.Stmt (fun _ : K' => Bool) L' S'
  | .push k f q => .push (E.key k) (fun v => f (E.read v)) (stmt q)
  | .peek k f q => .peek (E.key k) (fun v x => E.write v (f (E.read v) x)) (stmt q)
  | .pop k f q => .pop (E.key k) (fun v x => E.write v (f (E.read v) x)) (stmt q)
  | .load f q => .load (fun v => E.write v (f (E.read v))) (stmt q)
  | .branch f q r => .branch (fun v => f (E.read v)) (stmt q) (stmt r)
  | .goto f => .goto (fun v => E.label (f (E.read v)))
  | .halt => E.stop

def cfg (a : TM2.Cfg (fun _ : K => Bool) L S) : TM2.Cfg (fun _ : K' => Bool) L' S' :=
  ⟨a.l.elim E.halted (fun l => some (E.label l)),E.state a.var,E.stack a.stk⟩

theorem stepAux_stmt (q : TM2.Stmt (fun _ : K => Bool) L S) (v : S) (s : K → List Bool) :
    TM2.stepAux (E.stmt q) (E.state v) (E.stack s)=E.cfg (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.stack_key,← E.stack_update]
      exact ih _ _
  | peek k f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.stack_key,E.write_state]
      exact ih _ _
  | pop k f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.stack_key,E.write_state,← E.stack_update]
      exact ih _ _
  | load f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.write_state]
      exact ih _ _
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [stmt,TM2.stepAux,E.read_state,h,Bool.cond_false,Bool.cond_true]
      · exact ihr _ _
      · exact ihq _ _
  | goto f => simp only [stmt,TM2.stepAux,E.read_state,cfg,Option.elim_some]
  | halt => exact E.stop_spec v s

theorem step_cfg (m : L → TM2.Stmt (fun _ : K => Bool) L S)
    (m' : L' → TM2.Stmt (fun _ : K' => Bool) L' S')
    (hm : ∀ l, m' (E.label l)=E.stmt (m l))
    (a b : TM2.Cfg (fun _ : K => Bool) L S) (h : TM2.step m a=some b) :
    TM2.step m' (E.cfg a)=some (E.cfg b) := by
  rcases a with ⟨l,v,s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b=TM2.stepAux (m l) v s := (Option.some.inj h).symm
      subst b
      simp only [cfg,Option.elim_some,TM2.step,hm]
      exact congrArg some (E.stepAux_stmt (m l) v s)

theorem trace (m : L → TM2.Stmt (fun _ : K => Bool) L S)
    (m' : L' → TM2.Stmt (fun _ : K' => Bool) L' S')
    (hm : ∀ l, m' (E.label l)=E.stmt (m l))
    {n : ℕ} {a b : TM2.Cfg (fun _ : K => Bool) L S} (h : Trace (TM2.step m) n a b) :
    Trace (TM2.step m') n (E.cfg a) (E.cfg b) :=
  h.map E.cfg (E.step_cfg m m' hm)

end Embedding
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanComposition -/
section
namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Turing Function

namespace Compose
variable (M N : Machine)

abbrev Key := M.K ⊕ (Unit ⊕ N.K)
abbrev Label := M.Label ⊕ (Bool ⊕ N.Label)
abbrev State := M.State × N.State × Option Bool

abbrev phaseLabel (b : Bool) : Label M N := .inr (.inl b)
abbrev auxiliary : Key M N := .inr (.inl ())

def left : Embedding M.K M.Label M.State (Key M N) (Label M N) (State M N) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,N.initial,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (fun _ => [])
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply,Sum.elim_inl,Sum.inl.injEq]
    · simp only [update_apply,Sum.elim_inr,Sum.inr_ne_inl,ite_false]
  label := Sum.inl
  halted := some (phaseLabel M N false)
  stop := .goto (fun _ => phaseLabel M N false)
  stop_spec _ _ := rfl

def right : Embedding N.K N.Label N.State (Key M N) (Label M N) (State M N) where
  key k := .inr (.inr k)
  read v := v.2.1
  write v x := (v.1,x,v.2.2)
  state v := (M.initial,v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim (fun _ => []) (Sum.elim (fun _ => []) s)
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply,Sum.elim_inl,Sum.inl_ne_inr,ite_false]
    · rcases j with j | j <;> simp only [update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inr.injEq,Sum.inl_ne_inr,ite_false]
  label l := .inr (.inr l)
  halted := none
  stop := .halt
  stop_spec _ _ := rfl

def source (b : Bool) : Key M N := if b then auxiliary M N else .inl M.output

def target (b : Bool) : Key M N := if b then .inr (.inr N.input) else auxiliary M N

 theorem source_ne_target (b : Bool) : source M N b ≠ target M N b := by
  cases b <;> simp [source,target,auxiliary]

def following (b : Bool) : Label M N :=
  if b then .inr (.inr N.main) else phaseLabel M N true

def clean (v : State M N) : State M N := (v.1,v.2.1,none)

def transfer (b : Bool) : TM2.Stmt (fun _ : Key M N => Bool) (Label M N) (State M N) :=
  .pop (source M N b) (fun v c => (v.1,v.2.1,c))
    (.branch (fun v => v.2.2.isSome)
      (.push (target M N b) (fun v => v.2.2.getD false)
        (.load (clean M N) (.goto (fun _ => phaseLabel M N b))))
      (.load (clean M N) (.goto (fun _ => following M N b))))

def code : Label M N → TM2.Stmt (fun _ : Key M N => Bool) (Label M N) (State M N)
  | .inl l => (left M N).stmt (M.code l)
  | .inr (.inl b) => transfer M N b
  | .inr (.inr l) => (right M N).stmt (N.code l)

abbrev machine : Machine where
  K := Key M N
  input := .inl M.input
  output := .inr (.inr N.output)
  Label := Label M N
  main := .inl M.main
  State := State M N
  initial := (M.initial,N.initial,none)
  code := code M N

 theorem code_left (l : M.Label) : (machine M N).code ((left M N).label l)=
    (left M N).stmt (M.code l) := rfl

 theorem code_right (l : N.Label) : (machine M N).code ((right M N).label l)=
    (right M N).stmt (N.code l) := rfl

 theorem initial_left (s : List Bool) : (left M N).cfg (M.initialCfg s)=
    (machine M N).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Embedding.cfg,left,Machine.initialCfg,machine]

 theorem final_right (s : List Bool) : (right M N).cfg (N.finalCfg s)=
    (machine M N).finalCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,right,Machine.finalCfg,machine]
  · rcases k with k | k <;> simp [Embedding.cfg,right,Machine.finalCfg,machine]

end Compose

def twoStacks {K : Type} [DecidableEq K] (a b : K) (xs ys : List Bool) (k : K) : List Bool :=
  if k=a then xs else if k=b then ys else []

@[simp] theorem twoStacks_source {K : Type} [DecidableEq K] (a b : K) (xs ys : List Bool) :
    twoStacks a b xs ys a=xs := by simp [twoStacks]

@[simp] theorem twoStacks_target {K : Type} [DecidableEq K] {a b : K} (h : a≠b)
    (xs ys : List Bool) : twoStacks a b xs ys b=ys := by simp [twoStacks,h.symm]

 theorem twoStacks_move {K : Type} [DecidableEq K] {a b : K} (h : a≠b)
    (x : Bool) (xs ys : List Bool) :
    update (update (twoStacks a b (x::xs) ys) a xs) b (x::ys)=twoStacks a b xs (x::ys) := by
  funext k
  by_cases ha : k=a
  · subst k; simp [h,twoStacks]
  · by_cases hb : k=b
    · subst k; simp [h.symm,twoStacks]
    · simp [ha,hb,twoStacks]

 theorem twoStacks_pop_empty {K : Type} [DecidableEq K] (a b : K) (ys : List Bool) :
    update (twoStacks a b [] ys) a []=twoStacks a b [] ys := by
  funext k
  by_cases h : k=a <;> simp [twoStacks,h]

namespace Compose
variable (M N : Machine)

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M N).Cfg :=
  ⟨some (phaseLabel M N b), (M.initial,N.initial,none),
    twoStacks (source M N b) (target M N b) xs ys⟩

 theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M N).step (transferCfg M N b (x::xs) ys)=
      some (transferCfg M N b xs (x::ys)) := by
  change some (TM2.stepAux (transfer M N b) (M.initial,N.initial,none)
    (twoStacks (source M N b) (target M N b) (x::xs) ys))=some (transferCfg M N b xs (x::ys))
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some,clean]
  rw [update_of_ne (Ne.symm (source_ne_target M N b)),twoStacks_target (source_ne_target M N b)]
  rw [twoStacks_move (source_ne_target M N b)]
  rfl

 theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M N).step xs.length (transferCfg M N b xs ys)
      (transferCfg M N b [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M N b x xs ys) (ih (x::ys))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M N).step (transferCfg M N b [] ys)=
      some ⟨some (following M N b),(M.initial,N.initial,none),
        twoStacks (source M N b) (target M N b) [] ys⟩ := by
  change some (TM2.stepAux (transfer M N b) (M.initial,N.initial,none)
    (twoStacks (source M N b) (target M N b) [] ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,clean,twoStacks_pop_empty]

 theorem left_final_transfer (xs : List Bool) :
    (left M N).cfg (M.finalCfg xs)=transferCfg M N false xs [] := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,left,Machine.finalCfg,transferCfg,twoStacks,source,target,auxiliary,Sum.inl.injEq,Sum.inl_ne_inr]
  · rcases k with k | k <;>
      simp [Embedding.cfg,left,Machine.finalCfg,transferCfg,twoStacks,source,target,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_change (ys : List Bool) :
    (machine M N).step (transferCfg M N false [] ys)=some (transferCfg M N true ys []) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [transferCfg,source,target,twoStacks,auxiliary,Sum.inl.injEq,Sum.inl_ne_inr]
  · rcases k with k | k <;> simp [transferCfg,source,target,twoStacks,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_end (ys : List Bool) :
    (machine M N).step (transferCfg M N true [] ys)=some ((right M N).cfg (N.initialCfg ys)) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,right,Machine.initialCfg,source,target,twoStacks,auxiliary,Sum.inl_ne_inr]
  · rcases k with k | k <;>
      simp [Embedding.cfg,right,Machine.initialCfg,source,target,twoStacks,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_full (xs : List Bool) :
    Trace (machine M N).step (2*xs.length+2)
      ((left M N).cfg (M.finalCfg xs)) ((right M N).cfg (N.initialCfg xs)) := by
  rw [left_final_transfer]
  have h₁ := transfer_run M N false xs []
  simp only [List.append_nil] at h₁
  have h₂ := Trace.cons (transfer_change M N xs.reverse) (transfer_run M N true xs.reverse [])
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃ := Trace.cons (transfer_end M N xs) (Trace.refl _)
  have hh := (h₁.trans h₂).trans h₃
  simpa only [show xs.length+(xs.length+1)+(0+1)=2*xs.length+2 by omega] using hh

 theorem run {s t u : List Bool} {n m : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg t))
    (hN : Trace N.step m (N.initialCfg t) (N.finalCfg u)) :
    Trace (machine M N).step (n+2*t.length+2+m)
      ((machine M N).initialCfg s) ((machine M N).finalCfg u) := by
  have h₁ := (left M N).trace M.code (machine M N).code (code_left M N) hM
  have h₂ := (right M N).trace N.code (machine M N).code (code_right M N) hN
  rw [initial_left] at h₁
  rw [final_right] at h₂
  have hh := (h₁.trans (transfer_full M N t)).trans h₂
  simpa only [Machine.step,machine,Nat.add_assoc] using hh

end Compose
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanPolynomial -/
section
namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

 theorem polynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n x =>
      simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left x (Nat.pow_le_pow_left h n)

structure PolyProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  machine : Machine
  time : Polynomial ℕ
  outputs : ∀ a, TM2OutputsInTime machine.tm (ea a) (some (eb (f a))) (time.eval (ea a).length)

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

def stock (P : PolyProgram ea eb f) : TM2ComputableInPolyTime ea eb f where
  tm := P.machine.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := P.time
  outputsFun a := by
    have h := P.outputs a
    dsimp only [Machine.tm,Equiv.refl] at h ⊢
    simpa only [List.map_id] using h

 theorem finite_work (P : PolyProgram ea eb f) (k : P.stock.tm.K) : Finite (P.stock.tm.Γ k) :=
  inferInstanceAs (Finite Bool)

 noncomputable def sizeBound (P : PolyProgram ea eb f) : Polynomial ℕ :=
  X+P.time*C P.machine.growth

 theorem length_bound (P : PolyProgram ea eb f) (a : α) :
    (eb (f a)).length ≤ P.sizeBound.eval (ea a).length := by
  simpa only [sizeBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    using P.machine.output_length (P.outputs a)

 noncomputable def compTime (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : Polynomial ℕ :=
  P.time+2*P.sizeBound+2+Q.time.comp P.sizeBound

 noncomputable def comp (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : PolyProgram ea ec (g ∘ f) where
  machine := Compose.machine P.machine Q.machine
  time := P.compTime Q
  outputs a := by
    let hP := P.outputs a
    let hQ := Q.outputs (f a)
    have tP : Trace P.machine.step hP.steps (P.machine.initialCfg (ea a))
        (P.machine.finalCfg (eb (f a))) := Trace.of_iterate hP.evals_in_steps
    have tQ : Trace Q.machine.step hQ.steps (Q.machine.initialCfg (eb (f a)))
        (Q.machine.finalCfg (ec (g (f a)))) := Trace.of_iterate hQ.evals_in_steps
    have h := Compose.run P.machine Q.machine tP tQ
    refine ⟨⟨_,h.iterate_eq⟩,?_⟩
    have hl := P.length_bound a
    have hqp := (hQ.steps_le_m).trans (polynomial_eval_mono Q.time hl)
    have hpp := hP.steps_le_m
    simp only [compTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_comp]
    omega

 def congr (P : PolyProgram ea eb f) (f' : α → β) (h : ∀ a, f a=f' a) : PolyProgram ea eb f' where
  machine := P.machine
  time := P.time
  outputs a := by rw [← h a]; exact P.outputs a

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanTransducer -/
section
namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

structure Transducer where
  Q : Type
  [finiteQ : Fintype Q]
  initial : Q
  next : Q → Bool → Q × List Bool
  finish : Q → List Bool
attribute [instance] Transducer.finiteQ

namespace Transducer
variable (T : Transducer)

def run : T.Q → List Bool → List Bool
  | q, [] => T.finish q
  | q, b::xs => (T.next q b).2 ++ run (T.next q b).1 xs

def width : ℕ := max (univ.sup (fun q => (T.finish q).length))
  (univ.sup (fun x : T.Q × Bool => (T.next x.1 x.2).2.length))

 theorem finish_length (q : T.Q) : (T.finish q).length ≤ T.width :=
  (le_sup (f:=fun q => (T.finish q).length) (mem_univ q)).trans (Nat.le_max_left _ _)

 theorem next_length (q : T.Q) (b : Bool) : (T.next q b).2.length ≤ T.width :=
  (le_sup (f:=fun x : T.Q × Bool => (T.next x.1 x.2).2.length) (mem_univ (q,b))).trans (Nat.le_max_right _ _)

 theorem run_length (q : T.Q) (xs : List Bool) : (T.run q xs).length ≤ T.width*(xs.length+1) := by
  induction xs generalizing q with
  | nil => simpa only [run,List.length_nil,zero_add,mul_one] using T.finish_length q
  | cons b xs ih =>
      have hn := T.next_length q b
      have ht := ih (T.next q b).1
      simp only [run,List.length_append,List.length_cons]
      rw [show xs.length+1+1=(xs.length+1)+1 by rfl,Nat.mul_add,mul_one]
      omega

inductive Key | input | buffer | output deriving DecidableEq
instance : Fintype Key := ⟨{Key.input,Key.buffer,Key.output},by
  intro k
  cases k <;> simp⟩
open Key
abbrev Label := T.Q ⊕ Unit
abbrev State := Option Bool

def emit : List Bool → TM2.Stmt (fun _ : Key => Bool) (Label T) State →
    TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | [], q => q
  | b::bs, q => .push buffer (fun _ => b) (emit bs q)

 theorem emit_step (bits : List Bool) (q : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (s : Key → List Bool) :
    TM2.stepAux (emit T bits q) v s=
      TM2.stepAux q v (update s buffer (bits.reverse++s buffer)) := by
  induction bits generalizing s with
  | nil => simp only [emit,List.reverse_nil,List.nil_append,update_eq_self]
  | cons b bs ih =>
      simp only [emit,TM2.stepAux,ih,update_self,update_idem,List.reverse_cons]
      simp only [List.append_assoc,List.singleton_append]

def transfer : TM2.Stmt (fun _ : Key => Bool) (Label T) State :=
  .pop buffer (fun _ b => b)
    (.branch Option.isSome
      (.push output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .inr ()))))
      (.load (fun _ => none) .halt))

def code : Label T → TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | .inl q => .pop input (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.load (fun _ => none) (emit T (T.next q true).2 (.goto (fun _ => .inl (T.next q true).1))))
          (.load (fun _ => none) (emit T (T.next q false).2 (.goto (fun _ => .inl (T.next q false).1)))))
        (.load (fun _ => none) (emit T (T.finish q) (.goto (fun _ => .inr ())))))
  | .inr _ => transfer T

abbrev machine : Machine where
  K := Key
  input := input
  output := output
  Label := Label T
  main := .inl T.initial
  State := State
  initial := none
  code := code T

def store (xs ys zs : List Bool) : Key → List Bool
  | input => xs
  | buffer => ys
  | output => zs

 theorem stacks_update_input (xs ys zs ts : List Bool) :
    update (store xs ys zs) input ts=store ts ys zs := by
  funext k
  cases k <;> simp [store]

 theorem stacks_update_buffer (xs ys zs ts : List Bool) :
    update (store xs ys zs) buffer ts=store xs ts zs := by
  funext k
  cases k <;> simp [store]

 theorem stacks_update_output (xs ys zs ts : List Bool) :
    update (store xs ys zs) output ts=store xs ys ts := by
  funext k
  cases k <;> simp [store]

def readCfg (q : T.Q) (xs ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inl q),none,store xs ys []⟩

def transferCfg (ys zs : List Bool) : (machine T).Cfg :=
  ⟨some (.inr ()),none,store [] ys zs⟩

 theorem read_cons (q : T.Q) (b : Bool) (xs ys : List Bool) :
    (machine T).step (T.readCfg q (b::xs) ys)=
      some (T.readCfg (T.next q b).1 xs ((T.next q b).2.reverse++ys)) := by
  cases b <;>
    simp [readCfg,TM2.step,code,TM2.stepAux,store,List.head?,List.tail,
      emit_step,stacks_update_input,stacks_update_buffer]

 theorem read_nil (q : T.Q) (ys : List Bool) :
    (machine T).step (T.readCfg q [] ys)=some (T.transferCfg ((T.finish q).reverse++ys) []) := by
  simp [readCfg,transferCfg,TM2.step,code,TM2.stepAux,store,List.head?,List.tail,
    emit_step,stacks_update_input,stacks_update_buffer]

 theorem read_run (q : T.Q) (xs ys : List Bool) :
    Trace (machine T).step (xs.length+1) (T.readCfg q xs ys)
      (T.transferCfg ((T.run q xs).reverse++ys) []) := by
  induction xs generalizing q ys with
  | nil => exact Trace.cons (T.read_nil q ys) (Trace.refl _)
  | cons b xs ih =>
      have h := Trace.cons (T.read_cons q b xs ys) (ih (T.next q b).1 ((T.next q b).2.reverse++ys))
      simpa only [run,List.reverse_append,List.append_assoc,List.length_cons] using h

 theorem transfer_cons (b : Bool) (ys zs : List Bool) :
    (machine T).step (T.transferCfg (b::ys) zs)=some (T.transferCfg ys (b::zs)) := by
  simp [transferCfg,TM2.step,code,transfer,TM2.stepAux,store,List.head?,List.tail,
    stacks_update_buffer,stacks_update_output]

 theorem transfer_nil (zs : List Bool) :
    (machine T).step (T.transferCfg [] zs)=some ((machine T).finalCfg zs) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [Machine.finalCfg,code,transfer,TM2.stepAux,store]

 theorem transfer_run (ys zs : List Bool) :
    Trace (machine T).step (ys.length+1) (T.transferCfg ys zs)
      ((machine T).finalCfg (ys.reverse++zs)) := by
  induction ys generalizing zs with
  | nil => exact Trace.cons (T.transfer_nil zs) (Trace.refl _)
  | cons b ys ih =>
      have h := Trace.cons (T.transfer_cons b ys zs) (ih (b::zs))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem run_trace (xs : List Bool) :
    Trace (machine T).step (xs.length+(T.run T.initial xs).length+2)
      ((machine T).initialCfg xs) ((machine T).finalCfg (T.run T.initial xs)) := by
  have hi : (machine T).initialCfg xs=T.readCfg T.initial xs [] := by
    apply cfg_ext <;> try rfl
    funext k
    cases k <;> simp [Machine.initialCfg,readCfg,store]
  rw [hi]
  have hr := T.read_run T.initial xs []
  simp only [List.append_nil] at hr
  have h := hr.trans (T.transfer_run (T.run T.initial xs).reverse [])
  simpa only [List.append_nil,List.length_reverse,List.reverse_reverse,
    show xs.length+1+((T.run T.initial xs).length+1)=xs.length+(T.run T.initial xs).length+2 by omega] using h

noncomputable def program : PolyProgram id id (T.run T.initial) where
  machine := machine T
  time := C (T.width+1)*X+C (T.width+2)
  outputs xs := by
    refine ⟨⟨_,(T.run_trace xs).iterate_eq⟩,?_⟩
    have hl := T.run_length T.initial xs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq]
    nlinarith

end Transducer
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanEncoding -/
section
namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def quote : List Bool → List Bool
  | [] => [false]
  | b::bs => true::b::quote bs

@[simp] theorem quote_length (bs : List Bool) : (quote bs).length=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [quote,List.length_cons,ih]; omega

def encodePair {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α × β) : List Bool :=
  quote (ea x.1)++eb x.2

@[simp] theorem encodePair_length {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α × β) :
    (encodePair ea eb x).length=2*(ea x.1).length+1+(eb x.2).length := by
  simp only [encodePair,List.length_append,quote_length]

namespace WordTransducer

def quoting : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[true,b])
  finish _ := [false]

 theorem quoting_run (xs : List Bool) : quoting.run () xs=quote xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [Transducer.run,quoting,List.cons_append,List.nil_append,quote] using congrArg (fun l => true::b::l) ih

def projecting (tail : Bool) : Transducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some (!b),[])
    | some false => (none,if tail then [] else [b])
    | some true => (some true,if tail then [b] else [])
  finish _ := []

 theorem projecting_done (tail : Bool) (xs : List Bool) :
    (projecting tail).run (some true) xs=if tail then xs else [] := by
  induction xs with
  | nil => cases tail <;> rfl
  | cons b xs ih =>
      change (if tail then [b] else [])++(projecting tail).run (some true) xs=_
      rw [ih]
      cases tail <;> simp

 theorem projecting_pair (tail : Bool) (xs ys : List Bool) :
    (projecting tail).run none (quote xs++ys)=if tail then ys else xs := by
  induction xs with
  | nil => exact projecting_done tail ys
  | cons b xs ih =>
      change (if tail then [] else [b])++(projecting tail).run none (quote xs++ys)=_
      rw [ih]
      cases tail <;> simp

end WordTransducer

namespace PolyProgram

 def of_word {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    {g : List Bool → List Bool} (P : PolyProgram id id g)
    (h : ∀ a, g (ea a)=eb (f a)) : PolyProgram ea eb f where
  machine := P.machine
  time := P.time
  outputs a := by simpa only [id_eq,h a] using P.outputs (ea a)

 noncomputable def quote : PolyProgram id id Binary.quote :=
  WordTransducer.quoting.program.congr _ WordTransducer.quoting_run

 noncomputable def fst {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) ea Prod.fst :=
  (WordTransducer.projecting false).program.of_word (fun _ => by
    simpa only [encodePair,Bool.false_eq_true,ite_false,WordTransducer.projecting] using WordTransducer.projecting_pair false _ _)

 noncomputable def snd {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) eb Prod.snd :=
  (WordTransducer.projecting true).program.of_word (fun _ => by
    simpa only [encodePair,ite_true,WordTransducer.projecting] using WordTransducer.projecting_pair true _ _)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanThread -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace Thread
variable (M : Machine)
abbrev Key := M.K ⊕ Bool
abbrev Label := M.Label ⊕ Fin 4
abbrev State := M.State × Option Bool
abbrev source : Key M := .inr false
abbrev buffer : Key M := .inr true
abbrev reading : Label M := .inr 0
abbrev loading : Label M := .inr 1
abbrev emitting : Label M := .inr 2
abbrev draining : Label M := .inr 3

def store (s : M.K → List Bool) (xs ys : List Bool) : Key M → List Bool :=
  fun k => match k with
  | .inl k => s k
  | .inr false => xs
  | .inr true => ys

@[simp] theorem store_local (s : M.K → List Bool) (xs ys : List Bool) (k : M.K) :
    store M s xs ys (.inl k)=s k := rfl
@[simp] theorem store_source (s : M.K → List Bool) (xs ys : List Bool) :
    store M s xs ys (source M)=xs := rfl
@[simp] theorem store_buffer (s : M.K → List Bool) (xs ys : List Bool) :
    store M s xs ys (buffer M)=ys := rfl

def slot (k : M.K) (xs : List Bool) : M.K → List Bool := fun j => if j=k then xs else []

 theorem slot_nil (k : M.K) : slot M k []=fun _ => [] := by funext j; simp [slot]
 theorem slot_self (k : M.K) (xs : List Bool) : slot M k xs k=xs := by simp [slot]
 theorem slot_update (k : M.K) (xs ys : List Bool) : update (slot M k xs) k ys=slot M k ys := by
  funext j
  by_cases h : j=k <;> simp [slot,h]

 theorem store_update_local (s : M.K → List Bool) (xs ys : List Bool) (k : M.K) (w : List Bool) :
    update (store M s xs ys) (.inl k) w=store M (update s k w) xs ys := by
  funext j
  rcases j with j | j
  · simp [store,update_apply]
  · cases j <;> simp [store]
 theorem store_update_source (s : M.K → List Bool) (xs ys w : List Bool) :
    update (store M s xs ys) (source M) w=store M s w ys := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]
 theorem store_update_buffer (s : M.K → List Bool) (xs ys w : List Bool) :
    update (store M s xs ys) (buffer M) w=store M s xs w := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]

def body (tail : List Bool) : Embedding M.K M.Label M.State (Key M) (Label M) (State M) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := store M s tail []
  stack_key _ _ := rfl
  stack_update s k x := (store_update_local M s tail [] k x).symm
  label := Sum.inl
  halted := some (emitting M)
  stop := .goto (fun _ => emitting M)
  stop_spec _ _ := rfl

 theorem body_stmt (tail : List Bool) (s : TM2.Stmt (fun _ : M.K => Bool) M.Label M.State) :
    (body M tail).stmt s=(body M []).stmt s := by
  induction s <;> simp_all [Embedding.stmt,body]

def clean (v : State M) : State M := (v.1,none)

def readCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (source M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.getD false)
      (.pop (source M) (fun v b => (v.1,b))
        (.push (buffer M) (fun v => v.2.getD false)
          (.load (clean M) (.goto (fun _ => reading M)))))
      (.load (clean M) (.goto (fun _ => loading M))))

def loadCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (.inl M.input) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => loading M))))
      (.load (clean M) (.goto (fun _ => .inl M.main))))

def emitCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (.inl M.output) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (buffer M) (fun _ => true) (.push (buffer M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => emitting M)))))
      (.push (buffer M) (fun _ => false)
        (.load (clean M) (.goto (fun _ => draining M)))))

def drainCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (source M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => draining M))))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M)
  | .inl l => (body M []).stmt (M.code l)
  | .inr i => if i=0 then readCode M else if i=1 then loadCode M else if i=2 then emitCode M else drainCode M

abbrev machine : Machine where
  K := Key M
  input := source M
  output := source M
  Label := Label M
  main := reading M
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (tail : List Bool) (l : M.Label) :
    (machine M).code ((body M tail).label l)=(body M tail).stmt (M.code l) := (body_stmt M tail _).symm

def readCfg (xs tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (reading M),(M.initial,none),store M (fun _ => []) (quote xs++tail) buf⟩

def loadCfg (tail buf xs : List Bool) : (machine M).Cfg :=
  ⟨some (loading M),(M.initial,none),store M (slot M M.input xs) tail buf⟩

def emitCfg (tail xs buf : List Bool) : (machine M).Cfg :=
  ⟨some (emitting M),(M.initial,none),store M (slot M M.output xs) tail buf⟩

def drainCfg (tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (draining M),(M.initial,none),store M (fun _ => []) tail buf⟩

 theorem read_cons (b : Bool) (xs tail buf : List Bool) :
    (machine M).step (readCfg M (b::xs) tail buf)=some (readCfg M xs tail (b::buf)) := by
  simp [readCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,store_update_buffer]

 theorem read_nil (tail buf : List Bool) :
    (machine M).step (readCfg M [] tail buf)=some (loadCfg M tail buf []) := by
  simp [readCfg,loadCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,slot_nil]

 theorem read_run (xs tail buf : List Bool) :
    Trace (machine M).step (xs.length+1) (readCfg M xs tail buf) (loadCfg M tail (xs.reverse++buf) []) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (read_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (read_cons M b xs tail buf) (ih (b::buf))

 theorem load_cons (b : Bool) (tail buf xs : List Bool) :
    (machine M).step (loadCfg M tail (b::buf) xs)=some (loadCfg M tail buf (b::xs)) := by
  simp [loadCfg,TM2.step,code,loadCode,TM2.stepAux,clean,
    store_update_buffer,store_update_local,slot_update,slot_self]

 theorem load_nil (tail xs : List Bool) :
    (machine M).step (loadCfg M tail [] xs)=some ((body M tail).cfg (M.initialCfg xs)) := by
  simp [loadCfg,Embedding.cfg,body,Machine.initialCfg,TM2.step,code,loadCode,TM2.stepAux,
    clean,store_update_buffer,slot]
  rfl

 theorem load_run (tail buf xs : List Bool) :
    Trace (machine M).step (buf.length+1) (loadCfg M tail buf xs)
      ((body M tail).cfg (M.initialCfg (buf.reverse++xs))) := by
  induction buf generalizing xs with
  | nil => exact Trace.cons (load_nil M tail xs) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (load_cons M b tail bs xs) (ih (b::xs))

 theorem emit_cons (b : Bool) (tail xs buf : List Bool) :
    (machine M).step (emitCfg M tail (b::xs) buf)=some (emitCfg M tail xs (b::true::buf)) := by
  simp [emitCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_update,slot_self]

 theorem emit_nil (tail buf : List Bool) :
    (machine M).step (emitCfg M tail [] buf)=some (drainCfg M tail (false::buf)) := by
  simp [emitCfg,drainCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_nil]

 theorem emit_run (tail xs buf : List Bool) :
    Trace (machine M).step (xs.length+1) (emitCfg M tail xs buf)
      (drainCfg M tail ((quote xs).reverse++buf)) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (emit_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,quote,List.reverse_cons,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        Trace.cons (emit_cons M b tail xs buf) (ih (b::true::buf))

 theorem drain_cons (b : Bool) (tail buf : List Bool) :
    (machine M).step (drainCfg M tail (b::buf))=some (drainCfg M (b::tail) buf) := by
  simp [drainCfg,TM2.step,code,drainCode,TM2.stepAux,clean,
    store_update_source,store_update_buffer]

 theorem drain_nil (tail : List Bool) :
    (machine M).step (drainCfg M tail [])=some ((machine M).finalCfg tail) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.finalCfg,code,drainCode,TM2.stepAux,clean]

 theorem drain_run (tail buf : List Bool) :
    Trace (machine M).step (buf.length+1) (drainCfg M tail buf) ((machine M).finalCfg (buf.reverse++tail)) := by
  induction buf generalizing tail with
  | nil => exact Trace.cons (drain_nil M tail) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (drain_cons M b tail bs) (ih (b::tail))

 theorem body_final (tail xs : List Bool) : (body M tail).cfg (M.finalCfg xs)=emitCfg M tail xs [] := rfl

 theorem run {xs zs : List Bool} {n : ℕ} (tail : List Bool)
    (h : Trace M.step n (M.initialCfg xs) (M.finalCfg zs)) :
    Trace (machine M).step (2*xs.length+3*zs.length+5+n)
      ((machine M).initialCfg (quote xs++tail)) ((machine M).finalCfg (quote zs++tail)) := by
  have hi : (machine M).initialCfg (quote xs++tail)=readCfg M xs tail [] := by
    apply cfg_ext <;> try rfl
    funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.initialCfg,readCfg,store]
  rw [hi]
  have ha := read_run M xs tail []
  simp only [List.append_nil] at ha
  have hb := load_run M tail xs.reverse []
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hb
  have hc := (body M tail).trace M.code (machine M).code (code_body M tail) h
  rw [body_final] at hc
  have hd := emit_run M tail zs []
  simp only [List.append_nil] at hd
  have he := drain_run M tail (quote zs).reverse
  simp only [List.reverse_reverse,List.length_reverse,quote_length] at he
  have hx := (((ha.trans hb).trans hc).trans hd).trans he
  convert hx using 1
  omega

end Thread

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {f : α → β}

 noncomputable def thread (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (encodePair ea ec) (encodePair eb ec) (fun x => (f x.1,x.2)) where
  machine := Thread.machine P.machine
  time := 2*X+3*P.sizeBound+5+P.time
  outputs x := by
    have hp := P.outputs x.1
    have h := Thread.run P.machine (ec x.2) (Trace.of_iterate hp.evals_in_steps)
    refine ⟨⟨_,h.iterate_eq⟩,?_⟩
    have hn : (ea x.1).length≤(encodePair ea ec x).length := by simp only [encodePair_length]; omega
    have hl := (P.length_bound x.1).trans (polynomial_eval_mono P.sizeBound hn)
    have ht := hp.steps_le_m.trans (polynomial_eval_mono P.time hn)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanParallelTransducer -/
section
namespace OAI


                                                 
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

structure ParallelTransducer where
  Q : Type
  [finiteQ : Fintype Q]
  initial : Q
  next : Q → Bool → Q × (List Bool × List Bool)
  finish : Q → List Bool × List Bool
attribute [instance] ParallelTransducer.finiteQ

namespace ParallelTransducer
variable (T : ParallelTransducer)

def run : T.Q → List Bool → List Bool × List Bool
  | q, [] => T.finish q
  | q, b::xs =>
    let v := T.next q b
    let z := run v.1 xs
    (v.2.1++z.1,v.2.2++z.2)

def width : ℕ := max (univ.sup (fun q => (T.finish q).1.length+(T.finish q).2.length))
  (univ.sup (fun x : T.Q × Bool => (T.next x.1 x.2).2.1.length+(T.next x.1 x.2).2.2.length))

 theorem finish_length (q : T.Q) : (T.finish q).1.length+(T.finish q).2.length≤T.width :=
  (le_sup (f:=fun q => (T.finish q).1.length+(T.finish q).2.length) (mem_univ q)).trans (Nat.le_max_left _ _)

 theorem next_length (q : T.Q) (b : Bool) :
    (T.next q b).2.1.length+(T.next q b).2.2.length≤T.width :=
  (le_sup (f:=fun x : T.Q × Bool => (T.next x.1 x.2).2.1.length+(T.next x.1 x.2).2.2.length)
    (mem_univ (q,b))).trans (Nat.le_max_right _ _)

 theorem run_length (q : T.Q) (xs : List Bool) :
    (T.run q xs).1.length+(T.run q xs).2.length≤T.width*(xs.length+1) := by
  induction xs generalizing q with
  | nil => simpa only [run,List.length_nil,zero_add,mul_one] using T.finish_length q
  | cons b xs ih =>
      have hn := T.next_length q b
      have ht := ih (T.next q b).1
      simp only [run,List.length_append,List.length_cons]
      rw [show xs.length+1+1=(xs.length+1)+1 by rfl,Nat.mul_add,mul_one]
      omega

abbrev Key := Fin 4
abbrev input : Key := 0
abbrev left : Key := 1
abbrev right : Key := 2
abbrev output : Key := 3
abbrev Label := T.Q ⊕ Bool
abbrev State := Option Bool

def store (xs ls rs ys : List Bool) : Key → List Bool :=
  fun k => if k=input then xs else if k=left then ls else if k=right then rs else ys

 theorem store_update_input (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) input zs=store zs ls rs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_left (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) left zs=store xs zs rs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_right (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) right zs=store xs ls zs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_output (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) output zs=store xs ls rs zs := by
  funext k
  fin_cases k <;> simp [store,input,left,right,output]

def emit (k : Key) : List Bool → TM2.Stmt (fun _ : Key => Bool) (Label T) State →
    TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | [], s => s
  | b::bs, s => .push k (fun _ => b) (emit k bs s)

 theorem emit_step (k : Key) (bits : List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (stk : Key → List Bool) :
    TM2.stepAux (emit T k bits s) v stk=TM2.stepAux s v (update stk k (bits.reverse++stk k)) := by
  induction bits generalizing stk with
  | nil => simp only [emit,List.reverse_nil,List.nil_append,update_eq_self]
  | cons b bs ih =>
      simp only [emit,TM2.stepAux,ih,update_self,update_idem,List.reverse_cons,
        List.append_assoc,List.singleton_append]

def emitPair (p : List Bool × List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State) :=
  emit T left p.1 (emit T right p.2 s)

 theorem emitPair_step (p : List Bool × List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (xs ls rs ys : List Bool) :
    TM2.stepAux (emitPair T p s) v (store xs ls rs ys)=
      TM2.stepAux s v (store xs (p.1.reverse++ls) (p.2.reverse++rs) ys) := by
  simp [emitPair,emit_step,store,input,left,right,store_update_left,store_update_right]

def transfer (phase : Bool) : TM2.Stmt (fun _ : Key => Bool) (Label T) State :=
  .pop (if phase then left else right) (fun _ b => b)
    (.branch Option.isSome
      (.push output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .inr phase))))
      (.load (fun _ => none) (if phase then .halt else .goto (fun _ => .inr true))))

def code : Label T → TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | .inl q => .pop input (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.load (fun _ => none) (emitPair T (T.next q true).2 (.goto (fun _ => .inl (T.next q true).1))))
          (.load (fun _ => none) (emitPair T (T.next q false).2 (.goto (fun _ => .inl (T.next q false).1)))))
        (.load (fun _ => none) (emitPair T (T.finish q) (.goto (fun _ => .inr false)))))
  | .inr b => transfer T b

abbrev machine : Machine where
  K := Key
  input := input
  output := output
  Label := Label T
  main := .inl T.initial
  State := State
  initial := none
  code := code T

def readCfg (q : T.Q) (xs ls rs : List Bool) : (machine T).Cfg :=
  ⟨some (.inl q),none,store xs ls rs []⟩
def rightCfg (ls rs ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inr false),none,store [] ls rs ys⟩
def leftCfg (ls ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inr true),none,store [] ls [] ys⟩

 theorem read_cons (q : T.Q) (b : Bool) (xs ls rs : List Bool) :
    (machine T).step (T.readCfg q (b::xs) ls rs)=
      some (T.readCfg (T.next q b).1 xs ((T.next q b).2.1.reverse++ls) ((T.next q b).2.2.reverse++rs)) := by
  cases b <;> simp [readCfg,TM2.step,code,TM2.stepAux,store,input,emitPair_step,store_update_input]

 theorem read_nil (q : T.Q) (ls rs : List Bool) :
    (machine T).step (T.readCfg q [] ls rs)=
      some (T.rightCfg ((T.finish q).1.reverse++ls) ((T.finish q).2.reverse++rs) []) := by
  simp [readCfg,rightCfg,TM2.step,code,TM2.stepAux,store,input,emitPair_step,store_update_input]

 theorem read_run (q : T.Q) (xs ls rs : List Bool) :
    Trace (machine T).step (xs.length+1) (T.readCfg q xs ls rs)
      (T.rightCfg ((T.run q xs).1.reverse++ls) ((T.run q xs).2.reverse++rs) []) := by
  induction xs generalizing q ls rs with
  | nil => exact Trace.cons (T.read_nil q ls rs) (Trace.refl _)
  | cons b xs ih =>
      simpa only [run,List.length_cons,List.reverse_append,List.append_assoc] using
        Trace.cons (T.read_cons q b xs ls rs)
          (ih (T.next q b).1 ((T.next q b).2.1.reverse++ls) ((T.next q b).2.2.reverse++rs))

 theorem right_cons (b : Bool) (ls rs ys : List Bool) :
    (machine T).step (T.rightCfg ls (b::rs) ys)=some (T.rightCfg ls rs (b::ys)) := by
  simp [rightCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_right,store_update_output]

 theorem right_nil (ls ys : List Bool) :
    (machine T).step (T.rightCfg ls [] ys)=some (T.leftCfg ls ys) := by
  simp [rightCfg,leftCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_right]

 theorem right_run (ls rs ys : List Bool) :
    Trace (machine T).step (rs.length+1) (T.rightCfg ls rs ys) (T.leftCfg ls (rs.reverse++ys)) := by
  induction rs generalizing ys with
  | nil => exact Trace.cons (T.right_nil ls ys) (Trace.refl _)
  | cons b rs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (T.right_cons b ls rs ys) (ih (b::ys))

 theorem left_cons (b : Bool) (ls ys : List Bool) :
    (machine T).step (T.leftCfg (b::ls) ys)=some (T.leftCfg ls (b::ys)) := by
  simp [leftCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_left,store_update_output]

 theorem left_nil (ys : List Bool) :
    (machine T).step (T.leftCfg [] ys)=some ((machine T).finalCfg ys) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    fin_cases k <;> simp [Machine.finalCfg,code,transfer,TM2.stepAux,store,input,left,right,output]

 theorem left_run (ls ys : List Bool) :
    Trace (machine T).step (ls.length+1) (T.leftCfg ls ys) ((machine T).finalCfg (ls.reverse++ys)) := by
  induction ls generalizing ys with
  | nil => exact Trace.cons (T.left_nil ys) (Trace.refl _)
  | cons b ls ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (T.left_cons b ls ys) (ih (b::ys))

 theorem run_trace (xs : List Bool) :
    Trace (machine T).step (xs.length+(T.run T.initial xs).1.length+(T.run T.initial xs).2.length+3)
      ((machine T).initialCfg xs)
      ((machine T).finalCfg ((T.run T.initial xs).1++(T.run T.initial xs).2)) := by
  have hi : (machine T).initialCfg xs=T.readCfg T.initial xs [] [] := by
    apply cfg_ext <;> try rfl
    funext k
    fin_cases k <;> simp [Machine.initialCfg,readCfg,store,input,left,right]
  rw [hi]
  have hr := T.read_run T.initial xs [] []
  simp only [List.append_nil] at hr
  have hs := T.right_run (T.run T.initial xs).1.reverse (T.run T.initial xs).2.reverse []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hs
  have ht := T.left_run (T.run T.initial xs).1.reverse (T.run T.initial xs).2
  simp only [List.length_reverse,List.reverse_reverse] at ht
  have h := (hr.trans hs).trans ht
  convert h using 1
  omega

noncomputable def program : PolyProgram id id (fun xs => (T.run T.initial xs).1++(T.run T.initial xs).2) where
  machine := machine T
  time := C (T.width+1)*X+C (T.width+3)
  outputs xs := by
    refine ⟨⟨_,(T.run_trace xs).iterate_eq⟩,?_⟩
    have hl := T.run_length T.initial xs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq]
    nlinarith

end ParallelTransducer
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanProducts -/
section
namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace WordTransducer

def identity : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[b])
  finish _ := []

 theorem identity_run (xs : List Bool) : identity.run () xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::identity.run () xs=b::xs; rw [ih]

def constant (s : List Bool) : Transducer where
  Q := Unit
  initial := ()
  next _ _ := ((),[])
  finish _ := s

 theorem constant_run (s xs : List Bool) : (constant s).run () xs=s := by
  induction xs with
  | nil => rfl
  | cons b xs ih => exact ih

def duplicate : ParallelTransducer where
  Q := Unit
  initial := ()
  next _ b := ((),([true,b],[b]))
  finish _ := ([false],[])

 theorem duplicate_run (xs : List Bool) : duplicate.run () xs=(quote xs,xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true::b::(duplicate.run () xs).1,b::(duplicate.run () xs).2)=_
      rw [ih]
      rfl

def exchange : ParallelTransducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some (!b),([],[]))
    | some false => (none,([],[b]))
    | some true => (some true,([true,b],[]))
  finish _ := ([false],[])

 theorem exchange_done (xs : List Bool) : exchange.run (some true) xs=(quote xs,[]) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true::b::(exchange.run (some true) xs).1,(exchange.run (some true) xs).2)=_
      rw [ih]
      rfl

 theorem exchange_run (xs ys : List Bool) : exchange.run none (quote xs++ys)=(quote ys,xs) := by
  induction xs with
  | nil => exact exchange_done ys
  | cons b xs ih =>
      change ((exchange.run none (quote xs++ys)).1,b::(exchange.run none (quote xs++ys)).2)=_
      rw [ih]

end WordTransducer

namespace PolyProgram
variable {α β γ δ : Type}
variable {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {ed : δ → List Bool}
variable {f : α → β} {g : γ → δ}

noncomputable def identity (ea : α → List Bool) : PolyProgram ea ea _root_.id :=
  WordTransducer.identity.program.of_word (fun a => by
    simpa only [WordTransducer.identity,id_eq] using WordTransducer.identity_run (ea a))

noncomputable def constant (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    PolyProgram ea eb (fun _ => b) :=
  (WordTransducer.constant (eb b)).program.of_word (fun a => by
    simpa only [WordTransducer.constant] using WordTransducer.constant_run (eb b) (ea a))

noncomputable def duplicate (ea : α → List Bool) : PolyProgram ea (encodePair ea ea) (fun a => (a,a)) :=
  WordTransducer.duplicate.program.of_word (fun a => by
    have h := congrArg (fun p : List Bool × List Bool => p.1++p.2) (WordTransducer.duplicate_run (ea a))
    simpa only [WordTransducer.duplicate,encodePair] using h)

noncomputable def exchange (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) (encodePair eb ea) Prod.swap :=
  WordTransducer.exchange.program.of_word (fun x => by
    have h := congrArg (fun p : List Bool × List Bool => p.1++p.2) (WordTransducer.exchange_run (ea x.1) (eb x.2))
    simpa only [WordTransducer.exchange,encodePair,Prod.swap] using h)

noncomputable def second (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (encodePair ec ea) (encodePair ec eb) (fun x => (x.1,f x.2)) :=
  (((exchange ec ea).comp (P.thread ec)).comp (exchange eb ec)).congr _ (fun _ => rfl)

noncomputable def product (P : PolyProgram ea eb f) (Q : PolyProgram ec ed g) :
    PolyProgram (encodePair ea ec) (encodePair eb ed) (fun x => (f x.1,g x.2)) :=
  ((P.thread ec).comp (Q.second eb)).congr _ (fun _ => rfl)

noncomputable def fanout {h : α → γ} (P : PolyProgram ea eb f) (Q : PolyProgram ea ec h) :
    PolyProgram ea (encodePair eb ec) (fun a => (f a,h a)) :=
  ((duplicate ea).comp (P.product Q)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanLoop -/
section
namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace Loop
variable (M : Machine)
abbrev Key := M.K ⊕ Unit
abbrev Label := M.Label ⊕ Option Bool
abbrev State := M.State × Option Bool
abbrev auxiliary : Key M := .inr ()
abbrev check : Label M := .inr none
abbrev phase (b : Bool) : Label M := .inr (some b)

def body : Embedding M.K M.Label M.State (Key M) (Label M) (State M) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (fun _ => [])
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j <;>
      simp only [update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr_ne_inl,ite_false]
  label := Sum.inl
  halted := some (check M)
  stop := .goto (fun _ => check M)
  stop_spec _ _ := rfl

def source (b : Bool) : Key M := if b then auxiliary M else .inl M.output

def target (b : Bool) : Key M := if b then .inl M.input else auxiliary M

 theorem source_ne_target (b : Bool) : source M b ≠ target M b := by
  cases b <;> simp [source,target,auxiliary]

def following (b : Bool) : Label M := if b then .inl M.main else phase M true

def clean (v : State M) : State M := (v.1,none)

def transfer (b : Bool) : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (source M b) (fun v c => (v.1,c))
    (.branch (fun v => v.2.isSome)
      (.push (target M b) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => phase M b))))
      (.load (clean M) (.goto (fun _ => following M b))))

def checkCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (.inl M.output) (fun v c => (v.1,c))
    (.branch (fun v => v.2.getD false)
      (.load (clean M) (.goto (fun _ => phase M false)))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M)
  | .inl l => (body M).stmt (M.code l)
  | .inr none => checkCode M
  | .inr (some b) => transfer M b

abbrev machine : Machine where
  K := Key M
  input := .inl M.input
  output := .inl M.output
  Label := Label M
  main := .inl M.main
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (l : M.Label) : (machine M).code ((body M).label l)=
    (body M).stmt (M.code l) := rfl

 theorem initial_body (s : List Bool) : (body M).cfg (M.initialCfg s)=
    (machine M).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Embedding.cfg,body,Machine.initialCfg]

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M).Cfg :=
  ⟨some (phase M b),(M.initial,none),twoStacks (source M b) (target M b) xs ys⟩

 theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M).step (transferCfg M b (x::xs) ys)=some (transferCfg M b xs (x::ys)) := by
  change some (TM2.stepAux (transfer M b) (M.initial,none)
    (twoStacks (source M b) (target M b) (x::xs) ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some,clean]
  rw [update_of_ne (Ne.symm (source_ne_target M b)),twoStacks_target (source_ne_target M b)]
  rw [twoStacks_move (source_ne_target M b)]
  rfl

 theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M).step xs.length (transferCfg M b xs ys)
      (transferCfg M b [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M b x xs ys) (ih (x::ys))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M).step (transferCfg M b [] ys)=
      some ⟨some (following M b),(M.initial,none),twoStacks (source M b) (target M b) [] ys⟩ := by
  change some (TM2.stepAux (transfer M b) (M.initial,none)
    (twoStacks (source M b) (target M b) [] ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,clean,twoStacks_pop_empty]

 theorem transfer_change (ys : List Bool) :
    (machine M).step (transferCfg M false [] ys)=some (transferCfg M true ys []) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [transferCfg,source,target,twoStacks,auxiliary]

 theorem transfer_end (ys : List Bool) :
    (machine M).step (transferCfg M true [] ys)=some ((machine M).initialCfg ys) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Machine.initialCfg,source,target,twoStacks,auxiliary]

 theorem transfer_full (xs : List Bool) :
    Trace (machine M).step (2*xs.length+2) (transferCfg M false xs []) ((machine M).initialCfg xs) := by
  have h₁ := transfer_run M false xs []
  simp only [List.append_nil] at h₁
  have h₂ := Trace.cons (transfer_change M xs.reverse) (transfer_run M true xs.reverse [])
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃ := Trace.cons (transfer_end M xs) (Trace.refl _)
  have hh := (h₁.trans h₂).trans h₃
  simpa only [show xs.length+(xs.length+1)+(0+1)=2*xs.length+2 by omega] using hh

def checkCfg (xs : List Bool) : (machine M).Cfg :=
  ⟨some (check M),(M.initial,none),fun k => if k=Sum.inl M.output then xs else []⟩

 theorem body_final (xs : List Bool) : (body M).cfg (M.finalCfg xs)=checkCfg M xs := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [body,Embedding.cfg,Machine.finalCfg,checkCfg]

 theorem check_step (b : Bool) (xs : List Bool) :
    (machine M).step (checkCfg M (b::xs))=
      some ⟨if b then some (phase M false) else none,(M.initial,none),
        fun k => if k=Sum.inl M.output then xs else []⟩ := by
  change some (TM2.stepAux (checkCode M) (M.initial,none)
    (fun k => if k=Sum.inl M.output then b::xs else []))=_
  simp only [checkCode,TM2.stepAux,List.head?_cons,List.tail_cons,
    Option.getD_some,clean,ite_true]
  cases b <;> simp only [Bool.cond_false,Bool.cond_true,Bool.false_eq_true,ite_false,ite_true]
  all_goals
    apply congrArg some
    apply cfg_ext <;> try rfl
    funext k
    by_cases h : k=Sum.inl M.output <;> simp [h]

 theorem check_false (xs : List Bool) :
    (machine M).step ((body M).cfg (M.finalCfg (false::xs)))=some ((machine M).finalCfg xs) := by
  rw [body_final,check_step]
  rfl

 theorem check_true (xs : List Bool) :
    (machine M).step ((body M).cfg (M.finalCfg (true::xs)))=some (transferCfg M false xs []) := by
  rw [body_final,check_step]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [transferCfg,twoStacks,source,target,auxiliary]

 theorem stop {s t : List Bool} {n : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg (false::t))) :
    Trace (machine M).step (n+1) ((machine M).initialCfg s) ((machine M).finalCfg t) := by
  have h := (body M).trace M.code (machine M).code (code_body M) hM
  rw [initial_body] at h
  exact h.trans (Trace.cons (check_false M t) (Trace.refl _))

 theorem next {s t u : List Bool} {n m : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg (true::t)))
    (hR : Trace (machine M).step m ((machine M).initialCfg t) ((machine M).finalCfg u)) :
    Trace (machine M).step (n+2*t.length+3+m) ((machine M).initialCfg s) ((machine M).finalCfg u) := by
  have h := (body M).trace M.code (machine M).code (code_body M) hM
  rw [initial_body] at h
  have hg := Trace.cons (check_true M t) (transfer_full M t)
  have hh := (h.trans hg).trans hR
  simpa only [Nat.add_assoc,show 2*t.length+2+1=2*t.length+3 by omega] using hh

end Loop

def encodeLoop {α β : Type} (ea : α → List Bool) (eb : β → List Bool) : β ⊕ α → List Bool
  | .inl b => false::eb b
  | .inr a => true::ea a

inductive BoundedRun {α β : Type} (ea : α → List Bool) (f : α → β ⊕ α) (S : ℕ) :
    ℕ → α → β → Prop
  | stop {a b} : (ea a).length ≤ S → f a=.inl b → BoundedRun ea f S 1 a b
  | step {a a' b n} : (ea a).length ≤ S → f a=.inr a' →
      BoundedRun ea f S n a' b → BoundedRun ea f S (n+1) a b

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → β ⊕ α}

noncomputable def passTime (P : PolyProgram ea (encodeLoop ea eb) f) (S : ℕ) : ℕ :=
  P.time.eval S+2*P.sizeBound.eval S+3

 theorem run_loop (P : PolyProgram ea (encodeLoop ea eb) f) {S n : ℕ} {a : α} {b : β}
    (h : BoundedRun ea f S n a b) :
    ∃ t ≤ n*P.passTime S, Trace (Loop.machine P.machine).step t
      ((Loop.machine P.machine).initialCfg (ea a)) ((Loop.machine P.machine).finalCfg (eb b)) := by
  induction h with
  | @stop a b ha hab =>
      have hp := P.outputs a
      have ht : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
          (P.machine.finalCfg (false::eb b)) := by
        have hh : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
            (P.machine.finalCfg (encodeLoop ea eb (f a))) := Trace.of_iterate hp.evals_in_steps
        simpa only [hab,encodeLoop] using hh
      refine ⟨hp.steps+1,?_,Loop.stop P.machine ht⟩
      have htime := hp.steps_le_m.trans (polynomial_eval_mono P.time ha)
      simp only [passTime,one_mul]
      omega
  | @step a a' b n ha haa' h ih =>
      obtain ⟨t,ht,htrace⟩ := ih
      have hp := P.outputs a
      have hb : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
          (P.machine.finalCfg (true::ea a')) := by
        have hh : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
            (P.machine.finalCfg (encodeLoop ea eb (f a))) := Trace.of_iterate hp.evals_in_steps
        simpa only [haa',encodeLoop] using hh
      refine ⟨hp.steps+2*(ea a').length+3+t,?_,Loop.next P.machine hb htrace⟩
      have htime := hp.steps_le_m.trans (polynomial_eval_mono P.time ha)
      have hl := (P.length_bound a).trans (polynomial_eval_mono P.sizeBound ha)
      simp only [haa',encodeLoop,List.length_cons] at hl
      dsimp only [passTime] at ht ⊢
      rw [Nat.add_mul]
      omega

noncomputable def loop (P : PolyProgram ea (encodeLoop ea eb) f) (g : α → β)
    (iterations sizes : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ iterations.eval (ea a).length,
      BoundedRun ea f (sizes.eval (ea a).length) n a (g a)) : PolyProgram ea eb g where
  machine := Loop.machine P.machine
  time := iterations*(P.time.comp sizes+2*P.sizeBound.comp sizes+3)
  outputs a := Classical.choice (show Nonempty _ from by
    obtain ⟨n,hn,hrun⟩ := h a
    obtain ⟨t,ht,htrace⟩ := P.run_loop hrun
    refine ⟨⟨⟨t,htrace.iterate_eq⟩,?_⟩⟩
    refine ht.trans ?_
    simpa only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_comp,
      Polynomial.eval_ofNat,passTime] using Nat.mul_le_mul_right (P.passTime (sizes.eval (ea a).length)) hn)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanListPrimitives -/
section
namespace OAI


                                             
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def encodeBool (b : Bool) : List Bool := [b]

namespace WordTransducer

def emptyTest : Transducer where
  Q := Bool
  initial := true
  next _ _ := (false,[])
  finish b := [b]

 theorem emptyTest_run (q : Bool) (xs : List Bool) :
    emptyTest.run q xs=[q && xs.isEmpty] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change emptyTest.run false xs=_
      rw [ih]
      simp

def head : Transducer where
  Q := Option Bool
  initial := none
  next q b := (q.or (some b),[])
  finish q := [q.getD false]

 theorem head_run (q : Option Bool) (xs : List Bool) :
    head.run q xs=[(q.or xs.head?).getD false] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change head.run (q.or (some b)) xs=_
      rw [ih]
      cases q <;> rfl

def tail : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then [] else [b])
  finish _ := []

 theorem tail_run_false (xs : List Bool) : tail.run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::tail.run false xs=b::xs; rw [ih]

 theorem tail_run (xs : List Bool) : tail.run true xs=xs.tail := by
  cases xs with
  | nil => rfl
  | cons b xs => exact tail_run_false xs

abbrev prepend : Transducer where
  Q := Fin 4
  initial := 0
  next q b := if q=0 then (1,[]) else if q=1 then (2,[b]) else if q=2 then (3,[]) else (3,[b])
  finish _ := []

 theorem prepend_done (xs : List Bool) : prepend.run 3 xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change b::prepend.run 3 xs=b::xs
      rw [ih]

 theorem prepend_run (b : Bool) (xs : List Bool) :
    prepend.run 0 (quote [b]++xs)=b::xs := by
  change b::prepend.run 3 xs=b::xs
  rw [prepend_done]

def prependWord (p : List Bool) : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then p++[b] else [b])
  finish q := if q then p else []

 theorem prefix_done (p xs : List Bool) : (prependWord p).run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::(prependWord p).run false xs=b::xs; rw [ih]

 theorem prefix_run (p xs : List Bool) : (prependWord p).run true xs=p++xs := by
  cases xs with
  | nil => exact (List.append_nil p).symm
  | cons b xs =>
      change (p++[b])++(prependWord p).run false xs=p++b::xs
      rw [prefix_done,List.append_assoc,List.singleton_append]

def select : Transducer where
  Q := Fin 2 ⊕ (Bool × Option (Option Bool))
  initial := .inl 0
  next q b := match q with
    | .inl k => if k=0 then (.inl 1,[]) else (.inr (b,none),[])
    | .inr (keep,none) => (.inr (keep,some none),[])
    | .inr (keep,some none) => (.inr (keep,some (some (!b))),[])
    | .inr (keep,some (some false)) => (.inr (keep,some none),if keep then [] else [b])
    | .inr (keep,some (some true)) => (.inr (keep,some (some true)),if keep then [b] else [])
  finish _ := []

 theorem select_done (keep : Bool) (xs : List Bool) :
    select.run (.inr (keep,some (some true))) xs=if keep then xs else [] := by
  induction xs with
  | nil => cases keep <;> rfl
  | cons b xs ih =>
      change (if keep then [b] else [])++select.run (.inr (keep,some (some true))) xs=_
      rw [ih]
      cases keep <;> simp

 theorem select_pair (keep : Bool) (xs ys : List Bool) :
    select.run (.inr (keep,some none)) (quote xs++ys)=if keep then ys else xs := by
  induction xs with
  | nil => exact select_done keep ys
  | cons b xs ih =>
      change (if keep then [] else [b])++select.run (.inr (keep,some none)) (quote xs++ys)=_
      rw [ih]
      cases keep <;> simp

 theorem select_run (keep : Bool) (xs ys : List Bool) :
    select.run (.inl 0) (quote [keep]++quote xs++ys)=if keep then ys else xs := by
  exact select_pair keep xs ys

end WordTransducer

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

noncomputable def isEmpty : PolyProgram id encodeBool List.isEmpty :=
  WordTransducer.emptyTest.program.of_word (fun xs => by
    simpa only [WordTransducer.emptyTest,Bool.true_and,encodeBool,id_eq] using WordTransducer.emptyTest_run true xs)

noncomputable def head : PolyProgram id encodeBool (fun xs => xs.head?.getD false) :=
  WordTransducer.head.program.of_word (fun xs => by
    simpa only [WordTransducer.head,Option.or,encodeBool,id_eq] using WordTransducer.head_run none xs)

noncomputable def tail : PolyProgram id id List.tail :=
  WordTransducer.tail.program.of_word (fun xs => by
    simpa only [WordTransducer.tail,id_eq] using WordTransducer.tail_run xs)

noncomputable def cons : PolyProgram (encodePair encodeBool id) id (fun x => x.1::x.2) :=
  WordTransducer.prepend.program.of_word (fun x => by
    simpa only [WordTransducer.prepend,encodePair,encodeBool,id_eq] using WordTransducer.prepend_run x.1 x.2)

noncomputable def prependWord (p : List Bool) : PolyProgram id id (fun xs => p++xs) :=
  (WordTransducer.prependWord p).program.of_word (fun xs => by
    simpa only [WordTransducer.prependWord,id_eq] using WordTransducer.prefix_run p xs)

noncomputable def injectLeft (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram eb (encodeLoop ea eb) Sum.inl :=
  (prependWord [false]).of_word (fun _ => rfl)

noncomputable def injectRight (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram ea (encodeLoop ea eb) Sum.inr :=
  (prependWord [true]).of_word (fun _ => rfl)

noncomputable def select (eb : β → List Bool) :
    PolyProgram (encodePair encodeBool (encodePair eb eb)) eb
      (fun x => if x.1 then x.2.2 else x.2.1) :=
  WordTransducer.select.program.of_word (fun x => by
    simpa only [WordTransducer.select,encodePair,encodeBool,List.append_assoc,apply_ite] using
      WordTransducer.select_run x.1 (eb x.2.1) (eb x.2.2))

noncomputable def ite {p : α → Bool} {f g : α → β}
    (P : PolyProgram ea encodeBool p) (F : PolyProgram ea eb f) (G : PolyProgram ea eb g) :
    PolyProgram ea eb (fun a => if p a then g a else f a) :=
  ((P.fanout (F.fanout G)).comp (select eb)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanRecode -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β α' β' : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {ea' : α' → List Bool} {eb' : β' → List Bool} {f : α → β} {f' : α' → β'}

def recode (P : PolyProgram ea eb f) (i : α' → α)
    (hi : ∀ a, ea (i a)=ea' a) (ho : ∀ a, eb (f (i a))=eb' (f' a)) :
    PolyProgram ea' eb' f' where
  machine := P.machine
  time := P.time
  outputs a := by
    have h := P.outputs (i a)
    rwa [hi,ho] at h

end MetricKMedian.Binary.PolyProgram
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryLists -/
section
namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

 def encodeList {α : Type} (ea : α → List Bool) : List α → List Bool
  | [] => []
  | a::as => quote (ea a)++encodeList ea as

namespace EncodedList
variable {α : Type} (ea : α → List Bool)
 theorem nil : encodeList ea []=[] := rfl
 theorem cons (a : α) (as : List α) : encodeList ea (a::as)=quote (ea a)++encodeList ea as := rfl
 theorem cons_length (a : α) (as : List α) : (encodeList ea (a::as)).length=2*(ea a).length+1+(encodeList ea as).length := by
  simp only [encodeList,List.length_append,quote_length]
 theorem length_le (as : List α) : as.length ≤ (encodeList ea as).length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [cons_length,List.length_cons]; omega
 theorem isEmpty (as : List α) : (encodeList ea as).isEmpty=as.isEmpty := by
  cases as with
  | nil => rfl
  | cons a as =>
      have h := cons_length ea a as
      apply List.isEmpty_eq_false_iff.mpr
      intro hz
      simp only [hz,List.length_nil] at h
      omega
 theorem append (as bs : List α) : encodeList ea (as++bs)=encodeList ea as++encodeList ea bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append,encodeList,ih,List.append_assoc]
 theorem reverse_length (as : List α) : (encodeList ea as.reverse).length=(encodeList ea as).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.reverse_cons,append,List.length_append,cons_length,nil,List.length_nil,ih]
      omega
 theorem member_length (as : List α) (a : α) (h : a∈as) : (ea a).length ≤ (encodeList ea as).length := by
  induction as with
  | nil => simp at h
  | cons b as ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl|h
      · rw [cons_length]; omega
      · have hh := ih h
        rw [cons_length]; omega
 theorem length_bound (as : List α) (L : ℕ) (h : ∀ a∈as, (ea a).length ≤ L) :
    (encodeList ea as).length ≤ as.length*(2*L+1) := by
  induction as with
  | nil => simp only [nil,List.length_nil,zero_mul,le_refl]
  | cons a as ih =>
      have ha := h a (by simp)
      have hh := ih (fun a ha => h a (by simp [ha]))
      rw [cons_length,List.length_cons]
      nlinarith
end EncodedList

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listIsEmpty : PolyProgram (encodeList ea) encodeBool List.isEmpty :=
  isEmpty.recode (encodeList ea) (fun _ => rfl) (fun as => by rw [EncodedList.isEmpty])

noncomputable def listUncons : PolyProgram (encodeList ea) (encodePair ea (encodeList ea))
    (fun as => (as.head?.getD a0,as.tail)) := by
  let raw : PolyProgram (encodeList ea) id (encodeList ea) := (identity id).recode (encodeList ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeList ea) id (Binary.quote (ea a0))
  refine (ite (listIsEmpty ea) raw deflt).recode id (fun _ => rfl) ?_
  intro as
  cases as with
  | nil => simp [encodePair,encodeList]
  | cons a as => rfl
noncomputable def listHead : PolyProgram (encodeList ea) ea (fun as => as.head?.getD a0) :=
  ((listUncons ea a0).comp (fst ea (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listTail : PolyProgram (encodeList ea) (encodeList ea) List.tail :=
  ((listUncons ea a0).comp (snd ea (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listCons : PolyProgram (encodePair ea (encodeList ea)) (encodeList ea) (fun x => x.1::x.2) :=
  (identity id).recode (encodePair ea (encodeList ea)) (fun _ => rfl) (fun _ => rfl)
end PolyProgram

namespace ListReverse
variable {α : Type} (ea : α → List Bool) (a0 : α)
abbrev enc : List α × List α → List Bool := encodePair (encodeList ea) (encodeList ea)
 def body (s : List α × List α) : List α ⊕ (List α × List α) :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,s.1.head?.getD a0::s.2)
 def result (s : List α × List α) : List α := s.1.reverse++s.2

noncomputable def program : PolyProgram (enc ea) (encodeLoop (enc ea) (encodeList ea)) (body a0) := by
  let px := PolyProgram.fst (encodeList ea) (encodeList ea)
  let py := PolyProgram.snd (encodeList ea) (encodeList ea)
  let hd := px.comp (PolyProgram.listHead ea a0)
  let tl := px.comp (PolyProgram.listTail ea a0)
  let newLast := (hd.fanout py).comp (PolyProgram.listCons ea)
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight (enc ea) (encodeList ea))
  let done := py.comp (PolyProgram.injectLeft (enc ea) (encodeList ea))
  exact (PolyProgram.ite (px.comp (PolyProgram.listIsEmpty ea)) recur done).congr _ (fun _ => rfl)

 theorem run (as bs : List α) (S : ℕ) (h : 2*(encodeList ea as).length+1+(encodeList ea bs).length ≤ S) :
    BoundedRun (enc ea) (body a0) S (as.length+1) (as,bs) (as.reverse++bs) := by
  induction as generalizing bs with
  | nil =>
      apply BoundedRun.stop
      · simpa only [enc,encodePair_length] using h
      · rfl
  | cons a as ih =>
      have hs : 2*(encodeList ea as).length+1+(encodeList ea (a::bs)).length ≤ S := by
        simp only [EncodedList.cons_length] at h ⊢
        omega
      have hr := BoundedRun.step (ea:=enc ea) (f:=body a0)
        (a:=(a::as,bs)) (a':=(as,a::bs))
        (by simpa only [enc,encodePair_length] using h) rfl (ih (a::bs) hs)
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

noncomputable def loop : PolyProgram (enc ea) (encodeList ea) result :=
  (program ea a0).loop result (X+1) X (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · have h := EncodedList.length_le ea s.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]; omega
    · simpa only [eval_X,enc,encodePair_length,result] using run ea a0 s.1 s.2
        (2*(encodeList ea s.1).length+1+(encodeList ea s.2).length) le_rfl)
end ListReverse

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listReverse : PolyProgram (encodeList ea) (encodeList ea) List.reverse :=
  (((identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList ea) [])).comp (ListReverse.loop ea a0)).congr _
    (fun _ => List.append_nil _)
noncomputable def listAppend : PolyProgram (encodePair (encodeList ea) (encodeList ea)) (encodeList ea) (fun x => x.1++x.2) :=
  (((listReverse ea a0).thread (encodeList ea)).comp (ListReverse.loop ea a0)).congr _
    (fun _ => by simp only [Function.comp_apply,ListReverse.result,List.reverse_reverse])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListFold -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListFold
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α)
variable (op : β × α → β)
abbrev enc : List α × β → List Bool := encodePair (encodeList ea) eb
 def body (s : List α × β) : β ⊕ (List α × β) :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,op (s.2,s.1.head?.getD a0))
 def result (s : List α × β) : β := s.1.foldl (fun b a => op (b,a)) s.2

noncomputable def program (P : PolyProgram (encodePair eb ea) eb op) :
    PolyProgram (enc ea eb) (encodeLoop (enc ea eb) eb) (body a0 op) := by
  let px := PolyProgram.fst (encodeList ea) eb
  let py := PolyProgram.snd (encodeList ea) eb
  let hd := px.comp (PolyProgram.listHead ea a0)
  let tl := px.comp (PolyProgram.listTail ea a0)
  let newLast := (py.fanout hd).comp P
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight (enc ea eb) eb)
  let done := py.comp (PolyProgram.injectLeft (enc ea eb) eb)
  exact (PolyProgram.ite (px.comp (PolyProgram.listIsEmpty ea)) recur done).congr _ (fun _ => rfl)

 theorem run (as : List α) (b : β) (S : ℕ)
    (h : ∀ pre suf, as=pre++suf → (enc ea eb (suf,pre.foldl (fun b a => op (b,a)) b)).length ≤ S) :
    BoundedRun (enc ea eb) (body a0 op) S (as.length+1) (as,b) (result op (as,b)) := by
  induction as generalizing b with
  | nil =>
      apply BoundedRun.stop
      · exact h [] [] rfl
      · rfl
  | cons a as ih =>
      have hs : ∀ pre suf, as=pre++suf →
          (enc ea eb (suf,pre.foldl (fun b a => op (b,a)) (op (b,a)))).length ≤ S := by
        intro pre suf he
        exact h (a::pre) suf (by simp only [List.cons_append,he])
      exact BoundedRun.step (h [] (a::as) rfl) rfl (ih (op (b,a)) hs)

noncomputable def loop (P : PolyProgram (encodePair eb ea) eb op) (B : Polynomial ℕ)
    (hB : ∀ (as : List α) (b : β) pre suf, as=pre++suf →
      (eb (pre.foldl (fun b a => op (b,a)) b)).length ≤ B.eval (enc ea eb (as,b)).length) :
    PolyProgram (enc ea eb) eb (result op) :=
  (program ea eb a0 op P).loop (result op) (X+1) (2*X+1+B) (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · have h := EncodedList.length_le ea s.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]; omega
    · apply run
      intro pre suf he
      have hh := hB s.1 s.2 pre suf he
      have hx : (encodeList ea suf).length ≤ (encodeList ea s.1).length := by
        rw [he,EncodedList.append,List.length_append]
        omega
      simp only [enc,encodePair_length] at hh ⊢
      simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
      omega)

 theorem linear_height (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1))
    (as : List α) (b : β) :
    (eb (as.foldl (fun b a => op (b,a)) b)).length ≤ (eb b).length+C*(encodeList ea as).length := by
  induction as generalizing b with
  | nil => simp only [List.foldl_nil,EncodedList.nil,List.length_nil,mul_zero,add_zero,le_refl]
  | cons a as ih =>
      have hh := ih (op (b,a))
      have ha := hop b a
      simp only [List.foldl_cons,EncodedList.cons_length]
      nlinarith

noncomputable def linearLoop (P : PolyProgram (encodePair eb ea) eb op) (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1)) :
    PolyProgram (enc ea eb) eb (result op) :=
  loop ea eb a0 op P ((Polynomial.C C+1)*X) (fun as b pre suf he => by
    have hh := linear_height ea eb op C hop pre b
    have hp : (encodeList ea pre).length ≤ (encodeList ea as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [eval_mul,eval_add,eval_C,eval_one,eval_X,enc,encodePair_length]
    nlinarith)
end ListFold

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {op : β × α → β}
noncomputable def listFold (P : PolyProgram (encodePair eb ea) eb op) (a0 : α) (B : Polynomial ℕ)
    (hB : ∀ (as : List α) (b : β) pre suf, as=pre++suf →
      (eb (pre.foldl (fun b a => op (b,a)) b)).length ≤ B.eval (encodePair (encodeList ea) eb (as,b)).length) :
    PolyProgram (encodePair (encodeList ea) eb) eb (fun x => x.1.foldl (fun b a => op (b,a)) x.2) :=
  ListFold.loop ea eb a0 op P B hB
noncomputable def listFoldLinear (P : PolyProgram (encodePair eb ea) eb op) (a0 : α) (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1)) :
    PolyProgram (encodePair (encodeList ea) eb) eb (fun x => x.1.foldl (fun b a => op (b,a)) x.2) :=
  ListFold.linearLoop ea eb a0 op P C hop
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanFinite -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Finset

namespace FiniteTransducer
variable {α β : Type} [Fintype α] (ea : α → List Bool) (eb : β → List Bool) (f : α → β)

noncomputable def prefixes : Finset (List Bool) :=
  univ.biUnion (fun a => (ea a).inits.toFinset)

 theorem mem_prefixes (a : α) (xs ys : List Bool) (h : xs++ys=ea a) : xs∈prefixes ea := by
  classical
  apply mem_biUnion.mpr
  refine ⟨a,mem_univ _,List.mem_toFinset.mpr ?_⟩
  exact (List.mem_inits _ _).mpr ⟨ys,h⟩

abbrev Q := Option {xs : List Bool // xs∈prefixes ea}

noncomputable def state (xs : List Bool) : Q ea :=
  if h : xs∈prefixes ea then some ⟨xs,h⟩ else none

noncomputable abbrev table : Transducer where
  Q := Q ea
  initial := state ea []
  next q b := (match q with | none => none | some xs => state ea (xs.val++[b]),[])
  finish q := match q with
    | none => []
    | some xs => if h : ∃ a, ea a=xs.val then eb (f (Classical.choose h)) else []

 theorem next_state (xs : List Bool) (b : Bool) (h : xs∈prefixes ea) :
    (table ea eb f).next (state ea xs) b=(state ea (xs++[b]),[]) := by
  simp only [table,state,dif_pos h]

 theorem finish_state (a : α) (hinj : Injective ea) :
    (table ea eb f).finish (state ea (ea a))=eb (f a) := by
  have hm := mem_prefixes ea a (ea a) [] (List.append_nil _)
  have hex : ∃ a', ea a'=ea a := ⟨a,rfl⟩
  simp only [state,dif_pos hm,dif_pos hex]
  have he := Classical.choose_spec hex
  rw [hinj he]

 theorem run_state (a : α) (hinj : Injective ea) (xs ys : List Bool) (h : xs++ys=ea a) :
    (table ea eb f).run (state ea xs) ys=eb (f a) := by
  induction ys generalizing xs with
  | nil =>
      have he : xs=ea a := by simpa only [List.append_nil] using h
      rw [he]
      exact finish_state ea eb f a hinj
  | cons b ys ih =>
      change ((table ea eb f).next (state ea xs) b).2 ++
        (table ea eb f).run ((table ea eb f).next (state ea xs) b).1 ys = _
      rw [next_state ea eb f xs b (mem_prefixes ea a xs (b::ys) h),List.nil_append]
      apply ih
      simpa only [List.append_assoc,List.singleton_append] using h

noncomputable def program (hinj : Injective ea) : PolyProgram ea eb f :=
  (table ea eb f).program.of_word (fun a =>
    run_state ea eb f a hinj [] (ea a) rfl)

end FiniteTransducer

 theorem encodeBool_injective : Injective encodeBool := by
  intro a b h
  simpa only [encodeBool,List.cons.injEq,true_and,and_true] using h

 theorem quote_injective : Injective quote := by
  intro xs ys h
  have hh := congrArg ((WordTransducer.projecting false).run none) h
  have hx := WordTransducer.projecting_pair false xs []
  have hy := WordTransducer.projecting_pair false ys []
  simp only [List.append_nil,Bool.false_eq_true,ite_false] at hx hy
  rwa [hx,hy] at hh

 theorem encodePair_injective {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Injective ea) (hb : Injective eb) : Injective (encodePair ea eb) := by
  intro a b h
  have hx := congrArg ((WordTransducer.projecting false).run none) h
  have hy := congrArg ((WordTransducer.projecting true).run none) h
  simp only [encodePair,WordTransducer.projecting_pair,Bool.false_eq_true,ite_false,ite_true] at hx hy
  exact Prod.ext (ha hx) (hb hy)

namespace PolyProgram

noncomputable def boolFunction {α β : Type} [Fintype α] (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (hinj : Injective ea) : PolyProgram ea eb f :=
  FiniteTransducer.program ea eb f hinj

noncomputable def boolNot : PolyProgram encodeBool encodeBool Bool.not :=
  boolFunction _ _ _ encodeBool_injective
noncomputable def boolAnd : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 && x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)
noncomputable def boolOr : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 || x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanReverse -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ReverseLoop
abbrev S := List Bool × List Bool
abbrev enc : S → List Bool := encodePair id id

def body (s : S) : List Bool ⊕ S :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,s.1.head?.getD false::s.2)

def result (s : S) : List Bool := s.1.reverse++s.2

noncomputable def program : PolyProgram enc (encodeLoop enc id) body := by
  let first := PolyProgram.fst id id
  let last := PolyProgram.snd id id
  let hd := first.comp PolyProgram.head
  let tl := first.comp PolyProgram.tail
  let newLast := (hd.fanout last).comp PolyProgram.cons
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight enc id)
  let done := last.comp (PolyProgram.injectLeft enc id)
  exact (PolyProgram.ite (first.comp PolyProgram.isEmpty) recur done).congr _ (fun _ => rfl)

 theorem run (xs ys : List Bool) (S : ℕ) (h : 2*xs.length+1+ys.length≤S) :
    BoundedRun enc body S (xs.length+1) (xs,ys) (xs.reverse++ys) := by
  induction xs generalizing ys with
  | nil =>
      apply BoundedRun.stop
      · simpa only [enc,encodePair_length,id_eq,List.length_nil,zero_mul,zero_add] using h
      · rfl
  | cons b xs ih =>
      have hs : 2*xs.length+1+(b::ys).length≤S := by simp only [List.length_cons] at h ⊢; omega
      have hr := BoundedRun.step (ea:=enc) (f:=body)
        (a:=(b::xs,ys)) (a':=(xs,b::ys))
        (by simpa only [enc,encodePair_length,id_eq] using h) rfl (ih (b::ys) hs)
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

noncomputable def loop : PolyProgram enc id result :=
  program.loop result (X+1) X (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc,encodePair_length,id_eq]; omega
    · simpa only [eval_X,enc,encodePair_length,id_eq,result] using run s.1 s.2 (2*s.1.length+1+s.2.length) le_rfl)

end ReverseLoop

namespace PolyProgram
noncomputable def reverse : PolyProgram id id List.reverse :=
  (((identity id).fanout (constant id id [])).comp ReverseLoop.loop).congr _
    (fun _ => List.append_nil _)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryWords -/
section
namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs

@[simp] theorem value_nil : value []=0 := rfl
@[simp] theorem value_cons (b : Bool) (xs : List Bool) : value (b::xs)=b.toNat+2*value xs := rfl

 theorem value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn,value_cons,ih,Nat.bit_val]; omega

 theorem value_zero (xs : List Bool) : value xs=0 ↔ ∀ b∈xs,b=false := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [value_cons,Nat.add_eq_zero_iff,Nat.mul_eq_zero,OfNat.ofNat_ne_zero,false_or,Bool.toNat_eq_zero,ih,List.forall_mem_cons]

 theorem bits_value (xs : List Bool) (h : xs.getLast?≠some false) : (value xs).bits=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      by_cases he : xs=[]
      · subst xs
        cases b
        · exact False.elim (h rfl)
        · rfl
      · have ht : xs.getLast?≠some false := by
          intro hh
          apply h
          simp only [List.getLast?_cons,hh,Option.getD_some]
        rw [value_cons,show b.toNat+2*value xs=Nat.bit b (value xs) by rw [Nat.bit_val]; omega]
        rw [Nat.bits_append_bit,ih ht]
        intro hzero
        exfalso
        have hh := value_zero xs |>.mp hzero
        have hl := List.getLast_mem he
        have hb := hh _ hl
        apply ht
        rw [List.getLast?_eq_some_getLast he,hb]

 theorem value_append (xs ys : List Bool) : value (xs++ys)=value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [List.cons_append,value_cons,ih,List.length_cons,pow_succ]; ring

 theorem value_reverse_drop (xs : List Bool) : value (xs.dropWhile Bool.not).reverse=value xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · simp only [List.dropWhile_cons,Bool.not_false,ite_true,List.reverse_cons,value_append,
          value_cons,value_nil,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,zero_add]
        exact ih
      · simp

 theorem drop_head (xs : List Bool) : (xs.dropWhile Bool.not).head?≠some false := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all

 def normalize (xs : List Bool) : List Bool := (xs.reverse.dropWhile Bool.not).reverse

 theorem normalize_eq_bits (xs : List Bool) : normalize xs=(value xs).bits := by
  have hv : value (normalize xs)=value xs := by
    simpa only [normalize,List.reverse_reverse] using value_reverse_drop xs.reverse
  rw [← hv,bits_value]
  simp only [normalize,List.getLast?_reverse]
  exact drop_head _

end Word

namespace WordTransducer

def dropFalse : Transducer where
  Q := Bool
  initial := false
  next q b := (q || b,if q || b then [b] else [])
  finish _ := []

 theorem dropFalse_true (xs : List Bool) : dropFalse.run true xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::dropFalse.run true xs=b::xs; rw [ih]

 theorem dropFalse_run (xs : List Bool) : dropFalse.run false xs=xs.dropWhile Bool.not := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · exact ih
      · exact congrArg (List.cons true) (dropFalse_true xs)

end WordTransducer

namespace PolyProgram
noncomputable def append : PolyProgram (encodePair id id) id (fun x : List Bool × List Bool => x.1++x.2) :=
  ((reverse.thread id).comp ReverseLoop.loop).congr _ (fun x => by
    simp only [Function.comp_apply,ReverseLoop.result,List.reverse_reverse])

noncomputable def dropFalse : PolyProgram id id (List.dropWhile Bool.not) :=
  WordTransducer.dropFalse.program.of_word (fun xs => by
    simpa only [WordTransducer.dropFalse,id_eq] using WordTransducer.dropFalse_run xs)

noncomputable def normalize : PolyProgram id id Word.normalize :=
  ((reverse.comp dropFalse).comp reverse).congr _ (fun _ => rfl)

noncomputable def toBits : PolyProgram id Nat.bits Word.value :=
  normalize.of_word (fun xs => Word.normalize_eq_bits xs)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryAddition -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

def sumBit (a b c : Bool) : Bool := xor (xor a b) c
 def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

 theorem fullAdder (a b c : Bool) :
    (sumBit a b c).toNat+2*(carryBit a b c).toNat=a.toNat+b.toNat+c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

 def add : List Bool → List Bool → Bool → List Bool
  | [],[],c => if c then [true] else []
  | a::xs,ys,c => sumBit a (ys.head?.getD false) c :: add xs ys.tail (carryBit a (ys.head?.getD false) c)
  | [],b::ys,c => sumBit false b c :: add [] ys (carryBit false b c)
termination_by xs ys _ => xs.length+ys.length

 theorem add_step (xs ys : List Bool) (c : Bool) (h : (xs.isEmpty && ys.isEmpty)=false) :
    add xs ys c=sumBit (xs.head?.getD false) (ys.head?.getD false) c ::
      add xs.tail ys.tail (carryBit (xs.head?.getD false) (ys.head?.getD false) c) := by
  cases xs <;> cases ys <;> simp_all only [List.isEmpty_nil,List.isEmpty_cons,Bool.true_and,Bool.false_and,
    Bool.true_eq_false,List.head?_cons,List.head?_nil,Option.getD_some,Option.getD_none,
    List.tail_nil,List.tail_cons,add]

 theorem value_add (xs ys : List Bool) (c : Bool) : value (add xs ys c)=value xs+value ys+c.toNat := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [add,value]
      | cons b ys ih =>
          rw [add,value_cons,ih]
          have h := fullAdder false b c
          simp only [value_nil,value_cons,Bool.toNat_false] at *
          omega
  | cons a xs ih =>
      rw [add,value_cons,ih]
      have h := fullAdder a (ys.head?.getD false) c
      cases ys with
      | nil => simp only [List.head?_nil,Option.getD_none,List.tail_nil,value_nil,value_cons,Bool.toNat_false] at *; omega
      | cons b ys => simp only [List.head?_cons,Option.getD_some,List.tail_cons,value_cons] at *; omega

end Word

namespace AdditionLoop
abbrev S := List Bool × (List Bool × (Bool × List Bool))
abbrev ec : Bool × List Bool → List Bool := encodePair encodeBool id
abbrev ey : List Bool × (Bool × List Bool) → List Bool := encodePair id ec
abbrev enc : S → List Bool := encodePair id ey
 def empty (s : S) : Bool := s.1.isEmpty && s.2.1.isEmpty
 def next (s : S) : S :=
  (s.1.tail,(s.2.1.tail,(Word.carryBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1,
    Word.sumBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1 :: s.2.2.2)))
 def finish (s : S) : List Bool := (if s.2.2.1 then true::s.2.2.2 else s.2.2.2).reverse
 def body (s : S) : List Bool ⊕ S := if empty s then .inl (finish s) else .inr (next s)
 def result (s : S) : List Bool := s.2.2.2.reverse++Word.add s.1 s.2.1 s.2.2.1

 theorem enc_length (s : S) : (enc s).length=2*s.1.length+2*s.2.1.length+s.2.2.2.length+5 := by
  simp only [enc,ey,ec,encodePair_length,encodeBool,id_eq,List.length_cons,List.length_nil]
  omega

noncomputable def program : PolyProgram enc (encodeLoop enc id) body := by
  let px := PolyProgram.fst id ey
  let pyz := PolyProgram.snd id ey
  let py := pyz.comp (PolyProgram.fst id ec)
  let pca := pyz.comp (PolyProgram.snd id ec)
  let pc := pca.comp (PolyProgram.fst encodeBool id)
  let pa := pca.comp (PolyProgram.snd encodeBool id)
  let bits := (px.comp PolyProgram.head).fanout ((py.comp PolyProgram.head).fanout pc)
  let binj := encodePair_injective encodeBool_injective (encodePair_injective encodeBool_injective encodeBool_injective)
  let sb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.sumBit v.1 v.2.1 v.2.2) binj)
  let cb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.carryBit v.1 v.2.1 v.2.2) binj)
  let na := (sb.fanout pa).comp PolyProgram.cons
  let pn := (px.comp PolyProgram.tail).fanout ((py.comp PolyProgram.tail).fanout (cb.fanout na))
  let pe := ((px.comp PolyProgram.isEmpty).fanout (py.comp PolyProgram.isEmpty)).comp PolyProgram.boolAnd
  let pf := (PolyProgram.ite pc pa ((PolyProgram.constant enc encodeBool true).fanout pa |>.comp PolyProgram.cons)).comp PolyProgram.reverse
  exact (PolyProgram.ite pe (pn.comp (PolyProgram.injectRight enc id))
    (pf.comp (PolyProgram.injectLeft enc id))).congr _ (fun _ => rfl)

 theorem shorten (s : S) (h : empty s=false) :
    s.1.tail.length+s.2.1.tail.length<s.1.length+s.2.1.length := by
  rcases s with ⟨xs,ys,c,acc⟩
  cases xs <;> cases ys <;> simp_all [empty]
  omega

 theorem next_result (s : S) (h : empty s=false) : result (next s)=result s := by
  simp only [result]
  rw [Word.add_step s.1 s.2.1 s.2.2.1 h]
  simp only [next,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem next_size (s : S) (h : empty s=false) : (enc (next s)).length≤(enc s).length := by
  have hs := shorten s h
  simp only [enc_length,next,List.length_cons]
  omega

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.length+s.2.1.length=L → (enc s).length≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      cases he : empty s with
      | true =>
          refine ⟨1,by omega,BoundedRun.stop hs ?_⟩
          rcases s with ⟨xs,ys,c,acc⟩
          have hz : xs=[] ∧ ys=[] := by simpa only [empty,Bool.and_eq_true,List.isEmpty_iff] using he
          rcases hz with ⟨rfl,rfl⟩
          cases c <;> simp [body,empty,finish,result,Word.add]
      | false =>
          have hl : (next s).1.length+(next s).2.1.length<L := by simpa only [next,hL] using shorten s he
          obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl ((next_size s he).trans hs)
          refine ⟨n+1,by omega,?_⟩
          rw [next_result s he] at hr
          exact BoundedRun.step hs (by simp only [body,he,Bool.false_eq_true,ite_false]) hr

noncomputable def loop : PolyProgram enc id result :=
  program.loop result (X+1) X (fun s => by
    obtain ⟨n,hn,hr⟩ := run (s.1.length+s.2.1.length) s (enc s).length rfl le_rfl
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_X] using hr)

end AdditionLoop

namespace PolyProgram
noncomputable def addWords : PolyProgram (encodePair id id) id (fun x : List Bool × List Bool => Word.add x.1 x.2 false) := by
  let ex : List Bool × List Bool → List Bool := encodePair id id
  let init := (fst id id).fanout ((snd id id).fanout (constant ex AdditionLoop.ec (false,[])))
  exact (init.comp AdditionLoop.loop).congr _ (fun _ => rfl)

noncomputable def natAdd : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1+x.2) :=
  (addWords.comp toBits).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.value_add,Word.value_bits,Bool.toNat_false,Nat.add_zero])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryNatural -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word
 theorem normalize_length (xs : List Bool) : (normalize xs).length≤xs.length := by
  simpa only [normalize,List.length_reverse] using List.length_dropWhile_le Bool.not xs.reverse

 theorem bits_value_length (xs : List Bool) : (value xs).bits.length≤xs.length := by
  rw [← normalize_eq_bits]
  exact normalize_length xs
end Word

namespace NatBinary
 theorem zero_iff (n : ℕ) : n.bits=[] ↔ n=0 := by
  constructor
  · intro h
    have hv := Word.value_bits n
    rw [h,Word.value_nil] at hv
    exact hv.symm
  · rintro rfl; rfl

 theorem bit_length (b : Bool) (n : ℕ) : (Nat.bit b n).bits.length≤n.bits.length+1 := by
  have h := Word.bits_value_length (b::n.bits)
  simpa only [Word.value_cons,Word.value_bits,Nat.bit_val,Nat.add_comm,List.length_cons] using h

 theorem half_length (n : ℕ) : n.div2.bits.length=n.bits.length-1 := by
  rw [Nat.div2_bits_eq_tail,List.length_tail]

 theorem add_length (a b : ℕ) : (a+b).bits.length≤ max a.bits.length b.bits.length+1 := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (le_max_left a.size b.size))
  have hb := (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (le_max_right a.size b.size))
  rw [pow_succ]
  omega

 theorem mul_length (a b : ℕ) : (a*b).bits.length≤a.bits.length+b.bits.length := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  rw [pow_add]
  nlinarith

 theorem length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

 theorem half_lt_length {n : ℕ} (hn : n≠0) : n.div2.bits.length<n.bits.length := by
  rw [half_length]
  have hh : n.bits≠[] := fun h => hn ((zero_iff n).mp h)
  have hl : 0<n.bits.length := List.length_pos_iff.mpr hh
  omega
end NatBinary

namespace PolyProgram
noncomputable def natBit : PolyProgram (encodePair encodeBool Nat.bits) Nat.bits (fun x : Bool × ℕ => Nat.bit x.1 x.2) :=
  (cons.comp toBits).recode (fun x => (x.1,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.value_cons,Word.value_bits,Nat.bit_val,Nat.add_comm])

noncomputable def natHalf : PolyProgram Nat.bits Nat.bits Nat.div2 :=
  tail.recode Nat.bits (fun _ => rfl) (fun n => (Nat.div2_bits_eq_tail n).symm)

noncomputable def natOdd : PolyProgram Nat.bits encodeBool Nat.bodd :=
  head.recode Nat.bits (fun _ => rfl) (fun n => by
    rw [Nat.bodd_eq_bits_head]
    cases n.bits <;> rfl)

noncomputable def natZero : PolyProgram Nat.bits encodeBool (fun n => decide (n=0)) :=
  isEmpty.recode Nat.bits (fun _ => rfl) (fun n => by
    congr 1
    cases h : n.bits.isEmpty
    · have hn : n≠0 := by intro hn; subst n; contradiction
      exact (decide_eq_false hn).symm
    · have hn : n=0 := (NatBinary.zero_iff n).mp (List.isEmpty_iff.mp h)
      exact (decide_eq_true hn).symm)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListMap -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListAlgorithms
variable {α β : Type}
 theorem pushMap (f : α → β) (as : List α) (bs : List β) :
    as.foldl (fun bs a => f a::bs) bs=(as.map f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      rw [List.foldl_cons,ih,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem pushFilter (f : α → Bool) (as bs : List α) :
    as.foldl (fun bs a => if f a then a::bs else bs) bs=(as.filter f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons,List.filter_cons]
      cases f a <;> simp only [Bool.false_eq_true,ite_false,ite_true,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem count (as : List α) (n : ℕ) : as.foldl (fun n _ => n+1) n=n+as.length := by
  induction as generalizing n with
  | nil => rfl
  | cons a as ih => simp only [List.foldl_cons,ih,List.length_cons]; omega

 theorem all (p : α → Bool) (as : List α) (b : Bool) :
    as.foldl (fun b a => b && p a) b=(b && as.all p) := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.all_cons,Bool.and_assoc]

 theorem any (p : α → Bool) (as : List α) (b : Bool) :
    as.foldl (fun b a => b || p a) b=(b || as.any p) := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.any_cons,Bool.or_assoc]
end ListAlgorithms

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
noncomputable def listMap (P : PolyProgram ea eb f) (a0 : α) :
    PolyProgram (encodeList ea) (encodeList eb) (List.map f) := by
  let step : PolyProgram (encodePair (encodeList eb) ea) (encodeList eb) (fun x => f x.2::x.1) :=
    (((P.second (encodeList eb)).comp (exchange (encodeList eb) eb)).comp (listCons eb)).congr _ (fun _ => rfl)
  let fold := step.listFold a0 (X*(2*P.sizeBound+1)+X) (by
    intro as bs pre suf he
    simp only [ListAlgorithms.pushMap,EncodedList.append,List.length_append,EncodedList.reverse_length]
    let L := (encodePair (encodeList ea) (encodeList eb) (as,bs)).length
    have hpre : (encodeList ea pre).length ≤ (encodeList ea as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    have hlen : pre.length ≤ L := by
      have hp := EncodedList.length_le ea pre
      simp only [L,encodePair_length]; omega
    have hbs : (encodeList eb bs).length ≤ L := by simp only [L,encodePair_length]; omega
    have hh := EncodedList.length_bound eb (pre.map f) (P.sizeBound.eval L) (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      apply (P.length_bound a).trans
      apply polynomial_eval_mono
      have hmem := EncodedList.member_length ea pre a ha
      simp only [L,encodePair_length]; omega)
    simp only [List.length_map] at hh
    simp only [eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    change _ ≤ L*(2*P.sizeBound.eval L+1)+L
    nlinarith)
  let start := (identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList eb) [])
  exact ((start.comp fold).comp (listReverse eb (f a0))).congr _ (fun as => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.pushMap,List.append_nil,List.reverse_reverse])

noncomputable def listFilter {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) (encodeList ea) (List.filter p) := by
  let first := fst (encodeList ea) ea
  let test := (snd (encodeList ea) ea).comp P
  let push := (exchange (encodeList ea) ea).comp (listCons ea)
  let step : PolyProgram (encodePair (encodeList ea) ea) (encodeList ea) (fun x => if p x.2 then x.2::x.1 else x.1) :=
    (ite test first push).congr _ (fun _ => rfl)
  let fold := step.listFoldLinear a0 1 (by
    intro bs a
    simp only [one_mul]
    split_ifs
    · rw [EncodedList.cons_length]; omega
    · omega)
  exact ((((identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList ea) [])).comp fold).comp (listReverse ea a0)).congr _
    (fun as => by simp only [Function.comp_apply,id_eq,ListAlgorithms.pushFilter,List.append_nil,List.reverse_reverse])

noncomputable def listLength (ea : α → List Bool) (a0 : α) :
    PolyProgram (encodeList ea) Nat.bits List.length := by
  let step : PolyProgram (encodePair Nat.bits ea) Nat.bits (fun x : ℕ × α => x.1+1) :=
    (((fst Nat.bits ea).fanout (constant (encodePair Nat.bits ea) Nat.bits 1)).comp natAdd).congr _ (fun _ => rfl)
  let fold := step.listFoldLinear a0 2 (by
    intro n a
    have h := NatBinary.add_length n 1
    have hone : (1:ℕ).bits.length=1 := rfl
    rw [hone] at h
    dsimp only
    omega)
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) Nat.bits 0)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Nat.zero_add] using ListAlgorithms.count as 0)

noncomputable def listAll {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) encodeBool (fun as => as.all p) := by
  let step := (P.second encodeBool).comp boolAnd
  let fold := step.listFoldLinear a0 0 (by intro b a; simp only [encodeBool,List.length_singleton,zero_mul,add_zero,le_refl])
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) encodeBool true)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Bool.true_and] using ListAlgorithms.all p as true)

noncomputable def listAny {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) encodeBool (fun as => as.any p) := by
  let step := (P.second encodeBool).comp boolOr
  let fold := step.listFoldLinear a0 0 (by intro b a; simp only [encodeBool,List.length_singleton,zero_mul,add_zero,le_refl])
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) encodeBool false)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Bool.false_or] using ListAlgorithms.any p as false)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListContext -/
section
namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α β γ : Type}
 theorem pushMapWith (f : γ × α → β) (as : List α) (c : γ) (bs : List β) :
    as.foldl (fun x a => (x.1,f (x.1,a)::x.2)) (c,bs)=(c,(as.map (fun a => f (c,a))).reverse++bs) := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      simpa only [List.foldl_cons,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using ih (f (c,a)::bs)
 theorem pushMapWith_pair (f : γ × α → β) (as : List α) (x : γ × List β) :
    as.foldl (fun x a => (x.1,f (x.1,a)::x.2)) x=(x.1,(as.map (fun a => f (x.1,a))).reverse++x.2) := by
  cases x
  exact pushMapWith _ _ _ _
 theorem filterMapPair (p : γ × α → Bool) (c : γ) (as : List α) :
    (((as.map (fun a => (c,a))).filter p).map Prod.snd)=as.filter (fun a => p (c,a)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons,List.filter_cons]
      split <;> simp_all only [List.map_cons]
end ListAlgorithms

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def listMapWith {f : γ × α → β}
    (P : PolyProgram (encodePair ec ea) eb f) (a0 : α) (b0 : β) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList eb) (fun x => x.2.map (fun a => f (x.1,a))) := by
  let eacc := encodePair ec (encodeList eb)
  let acc := fst eacc ea
  let c := acc.comp (fst ec (encodeList eb))
  let bs := acc.comp (snd ec (encodeList eb))
  let a := snd eacc ea
  let nb := ((c.fanout a).comp P).fanout bs
  let step : PolyProgram (encodePair eacc ea) eacc (fun x : (γ × List β) × α => (x.1.1,f (x.1.1,x.2)::x.1.2)) :=
    (c.fanout (nb.comp (listCons eb))).congr _ (fun _ => rfl)
  let B : Polynomial ℕ := 3*X+X*(2*P.sizeBound.comp (3*X+1)+1)+1
  let fold := step.listFold a0 B (by
    intro as x pre suf he
    let L := (encodePair (encodeList ea) eacc (as,x)).length
    have hc : (ec x.1).length ≤ L := by simp only [L,eacc,encodePair_length]; omega
    have hb : (encodeList eb x.2).length ≤ L := by simp only [L,eacc,encodePair_length]; omega
    have hp : (encodeList ea pre).length ≤ L := by
      have hh : (encodeList ea pre).length ≤ (encodeList ea as).length := by rw [he,EncodedList.append,List.length_append]; omega
      simp only [L,encodePair_length]; omega
    have hplen : pre.length ≤ L := (EncodedList.length_le ea pre).trans hp
    have hout := EncodedList.length_bound eb (pre.map (fun a => f (x.1,a))) (P.sizeBound.eval (3*L+1)) (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      apply (P.length_bound (x.1,a)).trans
      apply polynomial_eval_mono
      have hla := (EncodedList.member_length ea pre a ha).trans hp
      simp only [encodePair_length]
      omega)
    rw [List.length_map] at hout
    simp only [ListAlgorithms.pushMapWith_pair,eacc,encodePair_length,EncodedList.append,List.length_append,EncodedList.reverse_length]
    simp only [B,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_comp]
    simp only [L,eacc,encodePair_length] at hc hb hplen hout
    nlinarith)
  let start := (snd ec (encodeList ea)).fanout ((fst ec (encodeList ea)).fanout (constant (encodePair ec (encodeList ea)) (encodeList eb) []))
  exact (((start.comp fold).comp (snd ec (encodeList eb))).comp (listReverse eb b0)).congr _ (fun x => by
    simp only [Function.comp_apply,ListAlgorithms.pushMapWith,List.append_nil,List.reverse_reverse])

noncomputable def listFilterWith {p : γ × α → Bool}
    (P : PolyProgram (encodePair ec ea) encodeBool p) (a0 : α) (c0 : γ) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList ea) (fun x => x.2.filter (fun a => p (x.1,a))) := by
  let attach := (identity (encodePair ec ea)).listMapWith a0 (c0,a0)
  let filt := listFilter P (c0,a0)
  let drop := (snd ec ea).listMap (c0,a0)
  exact ((attach.comp filt).comp drop).congr _ (fun x => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.filterMapPair])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListExtras -/
section
namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace WordTransducer

def listBits : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[true,b,false])
  finish _ := []
theorem listBits_run (xs : List Bool) : listBits.run () xs=encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change [true,b,false]++listBits.run () xs=quote [b]++encodeList encodeBool xs
      rw [ih]
      rfl
end WordTransducer
namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def wordAsList : PolyProgram id (encodeList encodeBool) id :=
  WordTransducer.listBits.program.of_word (fun xs => WordTransducer.listBits_run xs)
noncomputable def natAsList : PolyProgram Nat.bits (encodeList encodeBool) Nat.bits :=
  wordAsList.recode Nat.bits (fun _ => rfl) (fun _ => rfl)
noncomputable def natSize : PolyProgram Nat.bits Nat.bits Nat.size :=
  (natAsList.comp (listLength encodeBool false)).congr _ (fun n => Nat.size_eq_bits_len n)
noncomputable def listFlatten (ea : α → List Bool) (a0 : α) :
    PolyProgram (encodeList (encodeList ea)) (encodeList ea) List.flatten := by
  let P := (listAppend ea a0).listFoldLinear [] 1 (by
    intro bs as
    simp only [EncodedList.append,List.length_append]
    omega)
  exact (((identity (encodeList (encodeList ea))).fanout (constant (encodeList (encodeList ea)) (encodeList ea) [])).comp P).congr _ (fun xs => by
    change xs.foldl (fun b a => b++a) []=xs.flatten
    have he (xs : List (List α)) (acc : List α) : xs.foldl (fun b a => b++a) acc=acc++xs.flatten := by
      induction xs generalizing acc with
      | nil => simp
      | cons y ys hi => simpa only [List.foldl_cons,List.flatten_cons,List.append_assoc] using hi (acc++y)
    simpa using he xs [])
noncomputable def listFlatMap {f : α → List β} (P : PolyProgram ea (encodeList eb) f) (a0 : α) (b0 : β) :
    PolyProgram (encodeList ea) (encodeList eb) (fun xs => xs.flatMap f) :=
  ((P.listMap a0).comp (listFlatten eb b0)).congr _ (fun xs => by rfl)
noncomputable def listFlatMapWith {f : γ × α → List β} (P : PolyProgram (encodePair ec ea) (encodeList eb) f) (a0 : α) (b0 : β) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList eb) (fun x => x.2.flatMap (fun a => f (x.1,a))) :=
  ((P.listMapWith a0 []).comp (listFlatten eb b0)).congr _ (fun x => by rfl)
noncomputable def listAllWith {p : γ × α → Bool} (P : PolyProgram (encodePair ec ea) encodeBool p) (a0 : α) :
    PolyProgram (encodePair ec (encodeList ea)) encodeBool (fun x => x.2.all (fun a => p (x.1,a))) :=
  ((P.listMapWith a0 false).comp (listAll (identity encodeBool) false)).congr _ (fun x => by simp only [Function.comp_apply,List.all_map,Function.id_comp])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinarySubtraction -/
section
namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word
 def borrowBit (a b c : Bool) : Bool := ((!a) && b) || ((!a) && c) || (b && c)
 theorem fullSubtract (a b c : Bool) :
    a.toNat+2*(borrowBit a b c).toNat=b.toNat+c.toNat+(sumBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

 def sub : List Bool → List Bool → Bool → Bool × List Bool
  | [],[],c => (c,[])
  | a::xs,ys,c =>
      let t := sub xs ys.tail (borrowBit a (ys.head?.getD false) c)
      (t.1,sumBit a (ys.head?.getD false) c::t.2)
  | [],b::ys,c =>
      let t := sub [] ys (borrowBit false b c)
      (t.1,sumBit false b c::t.2)
termination_by xs ys _ => xs.length+ys.length

 theorem sub_step (xs ys : List Bool) (c : Bool) (h : (xs.isEmpty && ys.isEmpty)=false) :
    sub xs ys c=
      let t := sub xs.tail ys.tail (borrowBit (xs.head?.getD false) (ys.head?.getD false) c)
      (t.1,sumBit (xs.head?.getD false) (ys.head?.getD false) c::t.2) := by
  cases xs <;> cases ys <;> simp_all [sub]

 theorem value_lt (xs : List Bool) : value xs<2^xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
      have hb : b.toNat≤1 := by cases b <;> decide
      simp only [value_cons,List.length_cons,pow_succ]
      omega

 theorem value_sub (xs ys : List Bool) (c : Bool) :
    value (sub xs ys c).2+value ys+c.toNat=
      value xs+2^(sub xs ys c).2.length*(sub xs ys c).1.toNat := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => simp [sub,value]
      | cons b ys ih =>
          rw [sub]
          simp only [value_cons,value_nil,List.length_cons,pow_succ]
          have h := ih (borrowBit false b c)
          have hb := fullSubtract false b c
          simp only [value_nil,Bool.toNat_false] at h hb
          nlinarith
  | cons a xs ih =>
      rw [sub]
      simp only [value_cons,List.length_cons,pow_succ]
      have h := ih ys.tail (borrowBit a (ys.head?.getD false) c)
      have hb := fullSubtract a (ys.head?.getD false) c
      cases ys with
      | nil =>
          simp only [value_nil,List.head?_nil,Option.getD_none,List.tail_nil,Bool.toNat_false] at *
          nlinarith
      | cons b ys =>
          simp only [value_cons,List.head?_cons,Option.getD_some,List.tail_cons] at *
          nlinarith

 theorem sub_borrow (xs ys : List Bool) : (sub xs ys false).1=decide (value xs<value ys) := by
  have h := value_sub xs ys false
  have hl := value_lt (sub xs ys false).2
  cases he : (sub xs ys false).1
  · simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    have hn : ¬ value xs<value ys := by omega
    simp only [decide_eq_false hn]
  · simp only [he,Bool.toNat_true,Bool.toNat_false,Nat.mul_one,Nat.add_zero] at h
    have hn : value xs<value ys := by omega
    simp only [decide_eq_true hn]

 theorem sub_clamp (xs ys : List Bool) :
    value (if (sub xs ys false).1 then [] else (sub xs ys false).2)=value xs-value ys := by
  have h := value_sub xs ys false
  cases he : (sub xs ys false).1
  · simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    simp only [Bool.false_eq_true,ite_false]
    omega
  · have hl := sub_borrow xs ys
    rw [he] at hl
    have hn : value xs<value ys := of_decide_eq_true hl.symm
    simp only [ite_true,value_nil]
    omega
end Word

namespace SubtractionLoop
open AdditionLoop (S ec ey enc enc_length)
 def next (s : S) : S :=
  (s.1.tail,(s.2.1.tail,(Word.borrowBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1,
    Word.sumBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1 :: s.2.2.2)))
 def finish (s : S) : Bool × List Bool := (s.2.2.1,s.2.2.2.reverse)
 def body (s : S) : (Bool × List Bool) ⊕ S := if AdditionLoop.empty s then .inl (finish s) else .inr (next s)
 def result (s : S) : Bool × List Bool :=
  let t := Word.sub s.1 s.2.1 s.2.2.1
  (t.1,s.2.2.2.reverse++t.2)

noncomputable def program : PolyProgram enc (encodeLoop enc ec) body := by
  let px := PolyProgram.fst id ey
  let pyz := PolyProgram.snd id ey
  let py := pyz.comp (PolyProgram.fst id ec)
  let pca := pyz.comp (PolyProgram.snd id ec)
  let pc := pca.comp (PolyProgram.fst encodeBool id)
  let pa := pca.comp (PolyProgram.snd encodeBool id)
  let bits := (px.comp PolyProgram.head).fanout ((py.comp PolyProgram.head).fanout pc)
  let binj := encodePair_injective encodeBool_injective (encodePair_injective encodeBool_injective encodeBool_injective)
  let sb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.sumBit v.1 v.2.1 v.2.2) binj)
  let cb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.borrowBit v.1 v.2.1 v.2.2) binj)
  let na := (sb.fanout pa).comp PolyProgram.cons
  let pn := (px.comp PolyProgram.tail).fanout ((py.comp PolyProgram.tail).fanout (cb.fanout na))
  let pe := ((px.comp PolyProgram.isEmpty).fanout (py.comp PolyProgram.isEmpty)).comp PolyProgram.boolAnd
  let pf := pc.fanout (pa.comp PolyProgram.reverse)
  exact (PolyProgram.ite pe (pn.comp (PolyProgram.injectRight enc ec))
    (pf.comp (PolyProgram.injectLeft enc ec))).congr _ (fun _ => rfl)

 theorem next_result (s : S) (h : AdditionLoop.empty s=false) : result (next s)=result s := by
  simp only [result]
  rw [Word.sub_step s.1 s.2.1 s.2.2.1 h]
  simp only [next,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem next_size (s : S) (h : AdditionLoop.empty s=false) : (enc (next s)).length≤(enc s).length := by
  have hs := AdditionLoop.shorten s h
  simp only [enc_length,next,List.length_cons]
  omega

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.length+s.2.1.length=L → (enc s).length≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      cases he : AdditionLoop.empty s with
      | true =>
          refine ⟨1,by omega,BoundedRun.stop hs ?_⟩
          rcases s with ⟨xs,ys,c,acc⟩
          have hz : xs=[] ∧ ys=[] := by simpa only [AdditionLoop.empty,Bool.and_eq_true,List.isEmpty_iff] using he
          rcases hz with ⟨rfl,rfl⟩
          simp [body,AdditionLoop.empty,finish,result,Word.sub]
      | false =>
          have hl : (next s).1.length+(next s).2.1.length<L := by simpa only [next,hL] using AdditionLoop.shorten s he
          obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl ((next_size s he).trans hs)
          refine ⟨n+1,by omega,?_⟩
          rw [next_result s he] at hr
          exact BoundedRun.step hs (by simp only [body,he,Bool.false_eq_true,ite_false]) hr

noncomputable def loop : PolyProgram enc ec result :=
  program.loop result (X+1) X (fun s => by
    obtain ⟨n,hn,hr⟩ := run (s.1.length+s.2.1.length) s (enc s).length rfl le_rfl
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_X] using hr)
end SubtractionLoop

namespace PolyProgram
noncomputable def subWords : PolyProgram (encodePair id id) AdditionLoop.ec (fun x : List Bool × List Bool => Word.sub x.1 x.2 false) := by
  let ex : List Bool × List Bool → List Bool := encodePair id id
  let init := (fst id id).fanout ((snd id id).fanout (constant ex AdditionLoop.ec (false,[])))
  exact (init.comp SubtractionLoop.loop).congr _ (fun _ => rfl)

noncomputable def natLT : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1<x.2)) :=
  (subWords.comp (fst encodeBool id)).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.sub_borrow,Word.value_bits])

noncomputable def natSub : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1-x.2) := by
  let clamp := ite (fst encodeBool id) (snd encodeBool id) (constant AdditionLoop.ec id [])
  exact ((subWords.comp clamp).comp toBits).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.sub_clamp,Word.value_bits])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryDivision -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace DivisionLoop
 def qstep (b : Bool) (d q r : ℕ) : ℕ := Nat.bit (!decide (Nat.bit b r<d)) q
 def rstep (b : Bool) (d r : ℕ) : ℕ := if Nat.bit b r<d then Nat.bit b r else Nat.bit b r-d

 theorem step_total (b : Bool) (d q r : ℕ) :
    qstep b d q r*d+rstep b d r=2*(q*d+r)+b.toNat := by
  by_cases ht : Nat.bit b r<d
  · rw [qstep,rstep,if_pos ht,decide_eq_true ht]
    simp only [Bool.not_true,Nat.bit_val,Bool.toNat_false]
    ring
  · have hd : d≤Nat.bit b r := by omega
    have he := Nat.sub_add_cancel hd
    rw [qstep,rstep,if_neg ht,decide_eq_false ht]
    simp only [Bool.not_false,Nat.bit_val,Bool.toNat_true] at *
    nlinarith

 theorem step_remainder (b : Bool) (d r : ℕ) (_ : 0<d) (hr : r<d) : rstep b d r<d := by
  have hb : b.toNat≤1 := by cases b <;> decide
  unfold rstep
  split_ifs with ht
  · exact ht
  · simp only [Nat.bit_val] at *
    omega

 def eval : List Bool → ℕ → ℕ → ℕ → ℕ × ℕ
  | [],_,q,r => (q,r)
  | b::xs,d,q,r => eval xs d (qstep b d q r) (rstep b d r)

 theorem eval_spec (xs : List Bool) (d q r : ℕ) (hd : 0<d) (hr : r<d) :
    (eval xs d q r).2<d ∧
      (eval xs d q r).1*d+(eval xs d q r).2=2^xs.length*(q*d+r)+Word.value xs.reverse := by
  induction xs generalizing q r with
  | nil => exact ⟨hr,by simp [eval]⟩
  | cons b xs ih =>
      obtain ⟨hrem,heq⟩ := ih (qstep b d q r) (rstep b d r) (step_remainder b d r hd hr)
      refine ⟨hrem,?_⟩
      change (eval xs d (qstep b d q r) (rstep b d r)).1*d+
        (eval xs d (qstep b d q r) (rstep b d r)).2=_
      rw [heq,step_total]
      simp only [List.length_cons,List.reverse_cons,Word.value_append,Word.value_cons,Word.value_nil,
        Nat.mul_zero,Nat.add_zero,List.length_reverse,pow_succ]
      ring

abbrev S := List Bool × (ℕ × (ℕ × ℕ))
abbrev eqr : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
abbrev edqr : ℕ × (ℕ × ℕ) → List Bool := encodePair Nat.bits eqr
abbrev enc : S → List Bool := encodePair id edqr
 def next (s : S) : S :=
  (s.1.tail,(s.2.1,(qstep (s.1.head?.getD false) s.2.1 s.2.2.1 s.2.2.2,
    rstep (s.1.head?.getD false) s.2.1 s.2.2.2)))
 def body (s : S) : (ℕ × ℕ) ⊕ S := if s.1.isEmpty then .inl s.2.2 else .inr (next s)
 def result (s : S) : ℕ × ℕ := eval s.1 s.2.1 s.2.2.1 s.2.2.2
 def potential (s : S) : ℕ := s.1.length+max s.2.2.1.bits.length s.2.2.2.bits.length

 theorem enc_length (s : S) :
    (enc s).length=2*s.1.length+2*s.2.1.bits.length+2*s.2.2.1.bits.length+s.2.2.2.bits.length+3 := by
  simp only [enc,edqr,eqr,encodePair_length,id_eq]
  omega

 theorem total_le_length (s : S) : potential s+s.2.1.bits.length≤(enc s).length := by
  simp only [potential,enc_length]
  omega

 theorem length_le_total (s : S) : (enc s).length≤3*(potential s+s.2.1.bits.length)+3 := by
  simp only [potential,enc_length]
  omega

 theorem next_potential (s : S) (h : s.1.isEmpty=false) : potential (next s)≤potential s := by
  have hx : s.1.tail.length<s.1.length := by
    cases hh : s.1 with
    | nil => simp only [hh,List.isEmpty_nil] at h; contradiction
    | cons b xs => simp only [List.tail_cons,List.length_cons]; omega
  have hq := NatBinary.bit_length (!decide (Nat.bit (s.1.head?.getD false) s.2.2.2<s.2.1)) s.2.2.1
  have hr := NatBinary.bit_length (s.1.head?.getD false) s.2.2.2
  have hrle : rstep (s.1.head?.getD false) s.2.1 s.2.2.2≤Nat.bit (s.1.head?.getD false) s.2.2.2 := by
    unfold rstep
    split_ifs <;> omega
  have hrl := (NatBinary.length_mono hrle).trans hr
  simp only [potential,next,qstep]
  omega

 theorem next_result (s : S) (h : s.1.isEmpty=false) : result (next s)=result s := by
  rcases s with ⟨xs,d,q,r⟩
  cases xs with
  | nil => contradiction
  | cons b xs => rfl

noncomputable def program : PolyProgram enc (encodeLoop enc eqr) body := by
  let px := PolyProgram.fst id edqr
  let pdqr := PolyProgram.snd id edqr
  let pd := pdqr.comp (PolyProgram.fst Nat.bits eqr)
  let pqr := pdqr.comp (PolyProgram.snd Nat.bits eqr)
  let pq := pqr.comp (PolyProgram.fst Nat.bits Nat.bits)
  let pr := pqr.comp (PolyProgram.snd Nat.bits Nat.bits)
  let pb := px.comp PolyProgram.head
  let pt := (pb.fanout pr).comp PolyProgram.natBit
  let plt := (pt.fanout pd).comp PolyProgram.natLT
  let nq := ((plt.comp PolyProgram.boolNot).fanout pq).comp PolyProgram.natBit
  let nr := PolyProgram.ite plt ((pt.fanout pd).comp PolyProgram.natSub) pt
  let pn := (px.comp PolyProgram.tail).fanout (pd.fanout (nq.fanout nr))
  exact (PolyProgram.ite (px.comp PolyProgram.isEmpty)
    (pn.comp (PolyProgram.injectRight enc eqr))
    (pqr.comp (PolyProgram.injectLeft enc eqr))).congr _ (fun s => by
      simp only [Function.comp_apply,body,next,qstep,rstep,decide_eq_true_eq])

 theorem run (xs : List Bool) (d q r S : ℕ) (hs : 3*(potential (xs,d,q,r)+d.bits.length)+3≤S) :
    BoundedRun enc body S (xs.length+1) (xs,d,q,r) (result (xs,d,q,r)) := by
  induction xs generalizing q r with
  | nil =>
      exact BoundedRun.stop ((length_le_total ([],d,q,r)).trans hs) rfl
  | cons b xs ih =>
      let s : DivisionLoop.S := (b::xs,d,q,r)
      have hp := next_potential s rfl
      change 3*(potential s+d.bits.length)+3≤S at hs
      have hnext : 3*(potential (next s)+d.bits.length)+3≤S := by omega
      have hr := ih (qstep b d q r) (rstep b d r) hnext
      have hh : result (xs,d,qstep b d q r,rstep b d r)=result s := rfl
      rw [hh] at hr
      exact BoundedRun.step ((length_le_total s).trans hs) rfl hr

noncomputable def loop : PolyProgram enc eqr result :=
  program.loop result (X+1) (3*X+3) (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · simp only [Polynomial.eval_add,eval_X,eval_one,enc_length]; omega
    · have hs := total_le_length s
      simpa only [Polynomial.eval_add,eval_mul,eval_ofNat,eval_X] using
        run s.1 s.2.1 s.2.2.1 s.2.2.2 (3*(enc s).length+3) (by
          change 3*(potential s+s.2.1.bits.length)+3≤3*(enc s).length+3
          omega))
end DivisionLoop

namespace PolyProgram
noncomputable def natDivMod : PolyProgram (encodePair Nat.bits Nat.bits) (encodePair Nat.bits Nat.bits)
    (fun x : ℕ × ℕ => (x.1/x.2,x.1%x.2)) := by
  let ex : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
  let px := fst Nat.bits Nat.bits
  let pd := snd Nat.bits Nat.bits
  let rev : PolyProgram Nat.bits id (fun n => n.bits.reverse) := reverse.recode Nat.bits (fun _ => rfl) (fun _ => rfl)
  let init := (px.comp rev).fanout (pd.fanout (constant ex DivisionLoop.eqr (0,0)))
  let normal := init.comp DivisionLoop.loop
  let zeroCase := (constant ex Nat.bits 0).fanout px
  refine (ite (pd.comp natZero) normal zeroCase).congr _ ?_
  intro x
  change (if decide (x.2=0) then (0,x.1) else DivisionLoop.eval x.1.bits.reverse x.2 0 0)=_
  by_cases hd : x.2=0
  · simp only [hd,decide_true,ite_true,Nat.div_zero,Nat.mod_zero]
  · simp only [decide_eq_false hd,Bool.false_eq_true,ite_false]
    obtain ⟨hr,he⟩ := DivisionLoop.eval_spec x.1.bits.reverse x.2 0 0 (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero hd)
    simp only [zero_mul,zero_add,mul_zero,zero_add,List.reverse_reverse,Word.value_bits] at he
    have hp : x.1/x.2=(DivisionLoop.eval x.1.bits.reverse x.2 0 0).1 ∧
        x.1%x.2=(DivisionLoop.eval x.1.bits.reverse x.2 0 0).2 :=
      (Nat.div_mod_unique (Nat.pos_of_ne_zero hd)).mpr ⟨by
        simpa only [Nat.mul_comm,Nat.add_comm] using he,hr⟩
    exact Prod.ext hp.1.symm hp.2.symm

noncomputable def natDiv : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1/x.2) :=
  (natDivMod.comp (fst Nat.bits Nat.bits)).congr _ (fun _ => rfl)
noncomputable def natMod : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1%x.2) :=
  (natDivMod.comp (snd Nat.bits Nat.bits)).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryGCD -/
section
namespace OAI


                                 
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace NatBinary
 theorem mod_length_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : (a%b).bits.length < a.bits.length := by
  have ha : 0 < a := hb.trans_le hba
  by_cases hz : a%b=0
  · rw [hz,Nat.zero_bits,List.length_nil]
    apply List.length_pos_iff.mpr
    intro h
    have := (zero_iff a).mp h
    omega
  · have hr := Nat.mod_lt a hb
    have he := Nat.mod_add_div a b
    have hq : 1 ≤ a/b := (Nat.le_div_iff_mul_le hb).mpr (by simpa only [one_mul] using hba)
    have hm : b ≤ b*(a/b) := by nlinarith
    have hsmall : 2*(a%b) < a := by omega
    have hlen := length_mono hsmall.le
    have hbit : (2*(a%b)).bits.length=(a%b).bits.length+1 := by
      have hn : Nat.bit false (a%b) ≠ 0 := by
        simp only [Nat.bit_val,Bool.toNat_false,Nat.add_zero]
        omega
      simpa only [Nat.size_eq_bits_len,Nat.bit_val,Bool.toNat_false,Nat.add_zero,Nat.succ_eq_add_one]
        using Nat.size_bit hn
    omega
end NatBinary

namespace GCDLoop
abbrev S := ℕ × ℕ
abbrev enc : S → List Bool := encodePair Nat.bits Nat.bits
 def next (s : S) : S := (s.2,s.1%s.2)
 def body (s : S) : ℕ ⊕ S := if s.2=0 then .inl s.1 else .inr (next s)
 def result (s : S) : ℕ := s.1.gcd s.2
 def potential (s : S) : ℕ := s.1.bits.length+s.2.bits.length

 theorem enc_length (s : S) : (enc s).length=2*s.1.bits.length+1+s.2.bits.length := by
  exact encodePair_length _ _ _
 theorem length_le_potential (s : S) : (enc s).length ≤ 2*potential s+1 := by
  simp only [enc_length,potential]; omega
 theorem potential_le_length (s : S) : potential s ≤ (enc s).length := by
  simp only [enc_length,potential]; omega

 theorem next_result (s : S) : result (next s)=result s := by
  simp only [result,next]
  calc s.2.gcd (s.1%s.2)=(s.1%s.2).gcd s.2 := Nat.gcd_comm _ _
    _=s.2.gcd s.1 := (Nat.gcd_rec _ _).symm
    _=s.1.gcd s.2 := Nat.gcd_comm _ _

 theorem next_potential (s : S) : potential (next s) ≤ potential s := by
  have hm := NatBinary.length_mono (Nat.mod_le s.1 s.2)
  simp only [potential,next]
  omega

 theorem next_potential_lt (s : S) (ho : s.2 ≤ s.1) (hb : s.2 ≠ 0) : potential (next s) < potential s := by
  have h := NatBinary.mod_length_lt (Nat.pos_of_ne_zero hb) ho
  simp only [potential,next]
  omega

noncomputable def program : PolyProgram enc (encodeLoop enc Nat.bits) body := by
  let px := PolyProgram.fst Nat.bits Nat.bits
  let py := PolyProgram.snd Nat.bits Nat.bits
  let pn := py.fanout PolyProgram.natMod
  exact (PolyProgram.ite (py.comp PolyProgram.natZero)
    (pn.comp (PolyProgram.injectRight enc Nat.bits))
    (px.comp (PolyProgram.injectLeft enc Nat.bits))).congr _ (fun _ => by
      simp only [Function.comp_apply,body,next,decide_eq_true_eq])

 theorem run_ordered (L : ℕ) : ∀ (s : S) (S : ℕ), potential s=L →
    s.2 ≤ s.1 → 2*L+1 ≤ S → ∃ n ≤ L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL ho hs
      have hsize : (enc s).length ≤ S := (length_le_potential s).trans (by omega)
      by_cases hz : s.2=0
      · refine ⟨1,by omega,BoundedRun.stop hsize ?_⟩
        simp only [body,hz,ite_true,result,Nat.gcd_zero_right]
      · have hpot : potential (next s) < L := by simpa only [hL] using next_potential_lt s ho hz
        have horder : (next s).2 ≤ (next s).1 := (Nat.mod_lt s.1 (Nat.pos_of_ne_zero hz)).le
        obtain ⟨n,hn,hr⟩ := ih _ hpot (next s) S rfl horder (by omega)
        refine ⟨n+1,by omega,?_⟩
        rw [next_result] at hr
        exact BoundedRun.step hsize (by simp only [body,hz,ite_false]) hr

 theorem run (s : S) (S : ℕ) (hs : 2*potential s+1 ≤ S) :
    ∃ n ≤ potential s+2, BoundedRun enc body S n s (result s) := by
  by_cases ho : s.2 ≤ s.1
  · obtain ⟨n,hn,hr⟩ := run_ordered (potential s) s S rfl ho hs
    exact ⟨n,by omega,hr⟩
  · have hb : s.2 ≠ 0 := by omega
    have hn := next_potential s
    have horder : (next s).2 ≤ (next s).1 := (Nat.mod_lt s.1 (Nat.pos_of_ne_zero hb)).le
    obtain ⟨n,hbound,hr⟩ := run_ordered (potential (next s)) (next s) S rfl horder (by omega)
    refine ⟨n+1,by omega,?_⟩
    rw [next_result] at hr
    exact BoundedRun.step ((length_le_potential s).trans hs)
      (by simp only [body,hb,ite_false]) hr

noncomputable def loop : PolyProgram enc Nat.bits result :=
  program.loop result (X+2) (2*X+1) (fun s => by
    have hs := potential_le_length s
    obtain ⟨n,hn,hr⟩ := run s (2*(enc s).length+1) (by omega)
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_ofNat]; omega
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_one,eval_X] using hr)
end GCDLoop

namespace PolyProgram
noncomputable def natGcd : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1.gcd x.2) :=
  GCDLoop.loop
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryMultiplication -/
section
namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace MultiplicationLoop
abbrev S := ℕ × (ℕ × ℕ)
abbrev ey : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
abbrev enc : S → List Bool := encodePair Nat.bits ey
 def next (s : S) : S := (s.1.div2,(Nat.bit false s.2.1,if s.1.bodd then s.2.2+s.2.1 else s.2.2))
 def body (s : S) : ℕ ⊕ S := if s.1=0 then .inl s.2.2 else .inr (next s)
 def result (s : S) : ℕ := s.1*s.2.1+s.2.2
 def potential (s : S) : ℕ := s.1.bits.length+max s.2.1.bits.length s.2.2.bits.length

 theorem enc_length (s : S) : (enc s).length=2*s.1.bits.length+2*s.2.1.bits.length+s.2.2.bits.length+2 := by
  simp only [enc,ey,encodePair_length]
  omega

 theorem potential_le_length (s : S) : potential s≤(enc s).length := by
  simp only [potential,enc_length]
  omega

 theorem length_le_potential (s : S) : (enc s).length≤3*potential s+2 := by
  simp only [potential,enc_length]
  omega

 theorem next_potential (s : S) (h : s.1≠0) : potential (next s)≤potential s := by
  have hx := NatBinary.half_lt_length h
  have hy := NatBinary.bit_length false s.2.1
  have ha := NatBinary.add_length s.2.2 s.2.1
  simp only [potential,next]
  cases s.1.bodd <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

 theorem next_result (s : S) : result (next s)=result s := by
  have h := Nat.bodd_add_div2 s.1
  simp only [result,next,Nat.bit_val,Bool.toNat_false,Nat.add_zero]
  cases he : s.1.bodd
  · simp only [he,Bool.toNat_false,zero_add] at h
    simp only [Bool.false_eq_true,ite_false]
    nlinarith only [congrArg (fun n => n*s.2.1) h]
  · simp only [he,Bool.toNat_true] at h
    simp only [ite_true]
    nlinarith only [congrArg (fun n => n*s.2.1) h]

noncomputable def program : PolyProgram enc (encodeLoop enc Nat.bits) body := by
  let px := PolyProgram.fst Nat.bits ey
  let pyz := PolyProgram.snd Nat.bits ey
  let py := pyz.comp (PolyProgram.fst Nat.bits Nat.bits)
  let pa := pyz.comp (PolyProgram.snd Nat.bits Nat.bits)
  let half := px.comp PolyProgram.natHalf
  let twice := ((PolyProgram.constant enc encodeBool false).fanout py).comp PolyProgram.natBit
  let acc := PolyProgram.ite (px.comp PolyProgram.natOdd) pa ((pa.fanout py).comp PolyProgram.natAdd)
  let pn := half.fanout (twice.fanout acc)
  exact (PolyProgram.ite (px.comp PolyProgram.natZero)
    (pn.comp (PolyProgram.injectRight enc Nat.bits))
    (pa.comp (PolyProgram.injectLeft enc Nat.bits))).congr _ (fun s => by
      simp only [Function.comp_apply,body,decide_eq_true_eq]
      rfl)

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.bits.length=L → 3*potential s+2≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      have hsize := (length_le_potential s).trans hs
      by_cases hz : s.1=0
      · refine ⟨1,by omega,BoundedRun.stop hsize ?_⟩
        simp only [body,hz,ite_true,result,zero_mul,zero_add]
      · have hl : (next s).1.bits.length<L := by simpa only [next,hL] using NatBinary.half_lt_length hz
        have hb : 3*potential (next s)+2≤S := by have := next_potential s hz; omega
        obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl hb
        refine ⟨n+1,by omega,?_⟩
        rw [next_result] at hr
        exact BoundedRun.step hsize (by simp only [body,hz,ite_false]) hr

noncomputable def loop : PolyProgram enc Nat.bits result :=
  program.loop result (X+1) (3*X+2) (fun s => by
    obtain ⟨n,hn,hr⟩ := run s.1.bits.length s (3*(enc s).length+2) rfl (by
      have := potential_le_length s; omega)
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_X] using hr)
end MultiplicationLoop

namespace PolyProgram
noncomputable def natMul : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1*x.2) := by
  let ex : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
  let init := (fst Nat.bits Nat.bits).fanout ((snd Nat.bits Nat.bits).fanout (constant ex Nat.bits 0))
  exact (init.comp MultiplicationLoop.loop).congr _ (fun x => by
    simp only [Function.comp_apply,MultiplicationLoop.result,Nat.add_zero])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryInteger -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Signed
 def value (s : Bool) (n : ℕ) : ℤ := if s then -(n:ℤ) else n
 def sign (z : ℤ) : Bool := decide (z < 0)
 def parts (z : ℤ) : Bool × ℕ := (sign z,z.natAbs)
 def encode (z : ℤ) : List Bool := encodePair encodeBool Nat.bits (parts z)

 theorem abs_value (s : Bool) (n : ℕ) : (value s n).natAbs=n := by cases s <;> simp [value]
 theorem sign_value (s : Bool) (n : ℕ) : sign (value s n)=(s && !decide (n=0)) := by
  cases s <;> by_cases hn : n=0
  all_goals simp only [value,sign,Bool.false_eq_true,ite_false,ite_true]
  all_goals simp [hn, Nat.pos_of_ne_zero]

 theorem value_parts (z : ℤ) : value (sign z) z.natAbs=z := by
  unfold value sign
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt (of_decide_eq_true h))).symm
  · exact Int.natAbs_of_nonneg (by simpa using h)

 theorem value_neg (s : Bool) (n : ℕ) : value (!s) n= -value s n := by
  cases s <;> simp [value]

 theorem value_mul (s t : Bool) (n m : ℕ) : value (xor s t) (n*m)=value s n*value t m := by
  cases s <;> cases t <;> simp [value]

 def add (s t : Bool) (n m : ℕ) : ℤ :=
  if s=t then value s (n+m) else if n < m then value t (m-n) else value s (n-m)

 theorem value_add (s t : Bool) (n m : ℕ) : add s t n m=value s n+value t m := by
  cases s <;> cases t <;> by_cases h : n < m <;> simp [add,value,h] <;> omega

 theorem value_div (s : Bool) (n d : ℕ) (h : d∣n) : value s (n/d)=value s n/(d:ℤ) := by
  have hd : (d:ℤ)∣(n:ℤ) := Int.natCast_dvd_natCast.mpr h
  cases s <;> simp only [value,Bool.false_eq_true,ite_false,ite_true,Int.neg_ediv_of_dvd hd,Int.ofNat_ediv_ofNat]
end Signed

namespace PolyProgram
abbrev signedParts : Bool × ℕ → List Bool := encodePair encodeBool Nat.bits

noncomputable def intFromParts : PolyProgram signedParts Signed.encode (fun x => Signed.value x.1 x.2) := by
  let ps := fst encodeBool Nat.bits
  let pn := snd encodeBool Nat.bits
  let s := (ps.fanout ((pn.comp natZero).comp boolNot)).comp boolAnd
  exact (s.fanout pn).recode id (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,id_eq,Signed.encode,Signed.parts,Signed.sign_value,Signed.abs_value])

noncomputable def intSign : PolyProgram Signed.encode encodeBool Signed.sign :=
  (fst encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def intAbs : PolyProgram Signed.encode Nat.bits Int.natAbs :=
  (snd encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)

noncomputable def intNeg : PolyProgram Signed.encode Signed.encode Neg.neg :=
  (((intSign.comp boolNot).fanout intAbs).comp intFromParts).congr _ (fun z => by
    simp only [Function.comp_apply,Signed.value_neg,Signed.value_parts])

noncomputable def intOfNat : PolyProgram Nat.bits Signed.encode Nat.cast :=
  (((constant Nat.bits encodeBool false).fanout (identity Nat.bits)).comp intFromParts).congr _ (fun _ => rfl)

noncomputable def boolXor : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => xor x.1 x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)
noncomputable def boolEq : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => decide (x.1=x.2)) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

noncomputable def intMul : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1*x.2) := by
  let px := fst Signed.encode Signed.encode
  let py := snd Signed.encode Signed.encode
  let s := ((px.comp intSign).fanout (py.comp intSign)).comp boolXor
  let n := ((px.comp intAbs).fanout (py.comp intAbs)).comp natMul
  exact ((s.fanout n).comp intFromParts).congr _ (fun x => by
    simp only [Function.comp_apply,Signed.value_mul,Signed.value_parts])

noncomputable def intAdd : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1+x.2) := by
  let px := fst Signed.encode Signed.encode
  let py := snd Signed.encode Signed.encode
  let sx := px.comp intSign
  let sy := py.comp intSign
  let nx := px.comp intAbs
  let ny := py.comp intAbs
  let plus := ((sx.fanout ((nx.fanout ny).comp natAdd)).comp intFromParts)
  let minusX := (sx.fanout ((nx.fanout ny).comp natSub)).comp intFromParts
  let minusY := (sy.fanout ((ny.fanout nx).comp natSub)).comp intFromParts
  let minus := ite ((nx.fanout ny).comp natLT) minusX minusY
  refine (ite ((sx.fanout sy).comp boolEq) minus plus).congr _ ?_
  intro x
  simpa only [Function.comp_apply, decide_eq_true_eq, Signed.add, Signed.value_parts]
    using Signed.value_add (Signed.sign x.1) (Signed.sign x.2) x.1.natAbs x.2.natAbs

noncomputable def intSub : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1-x.2) :=
  ((intNeg.second Signed.encode).comp intAdd).congr _ (fun x => (sub_eq_add_neg x.1 x.2).symm)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryRational -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Ratio
 def parts (q : ℚ) : ℤ × ℕ := (q.num,q.den)
 def encode (q : ℚ) : List Bool := encodePair Signed.encode Nat.bits (parts q)
 def normalized (x : ℤ × ℕ) : ℤ × ℕ :=
  if x.2=0 then (0,1) else
    (Signed.value (Signed.sign x.1) (x.1.natAbs / x.2.gcd x.1.natAbs),x.2 / x.2.gcd x.1.natAbs)
 theorem normalized_eq (x : ℤ × ℕ) : normalized x=parts (mkRat x.1 x.2) := by
  simp only [normalized,parts,Rat.num_mkRat,Rat.den_mkRat]
  split_ifs with h
  · rfl
  · rw [Signed.value_div _ _ _ (Nat.gcd_dvd_right _ _),Signed.value_parts]

 theorem inv_eq (q : ℚ) : q⁻¹=mkRat (Signed.value (Signed.sign q.num) q.den) q.num.natAbs := by
  rw [Rat.mkRat_eq_div]
  calc
    q⁻¹ = ((q.num:ℚ)/q.den)⁻¹ := congrArg Inv.inv q.num_div_den.symm
    _ = (q.den:ℚ)/q.num := inv_div _ _
    _ = _ := by
      have hnum := Signed.value_parts q.num
      unfold Signed.value at hnum ⊢
      split_ifs with hn
      · rw [if_pos hn] at hnum
        have haZ : (q.num.natAbs:ℤ) = -q.num := by omega
        have ha : (q.num.natAbs:ℚ) = -(q.num:ℚ) := by simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z : ℤ => (z:ℚ)) haZ
        rw [Int.cast_neg,Int.cast_natCast,ha,neg_div_neg_eq]
      · rw [if_neg hn] at hnum
        have ha : (q.num.natAbs:ℚ) = (q.num:ℚ) := by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hnum
        rw [Int.cast_natCast,ha]
end Ratio

namespace PolyProgram
noncomputable def intLT : PolyProgram (encodePair Signed.encode Signed.encode) encodeBool (fun x : ℤ × ℤ => decide (x.1 < x.2)) :=
  (intSub.comp intSign).congr _ (fun _ => by simp only [Function.comp_apply,Signed.sign,sub_neg])
noncomputable def intEQ : PolyProgram (encodePair Signed.encode Signed.encode) encodeBool (fun x : ℤ × ℤ => decide (x.1=x.2)) :=
  ((intSub.comp intAbs).comp natZero).congr _ (fun _ => by simp only [Function.comp_apply,Int.natAbs_eq_zero,sub_eq_zero])

noncomputable def mkRational : PolyProgram (encodePair Signed.encode Nat.bits) Ratio.encode (fun x => mkRat x.1 x.2) := by
  let pn := fst Signed.encode Nat.bits
  let pd := snd Signed.encode Nat.bits
  let pa := pn.comp intAbs
  let pg := (pd.fanout pa).comp natGcd
  let nm := (((pn.comp intSign).fanout ((pa.fanout pg).comp natDiv)).comp intFromParts)
  let dm := (pd.fanout pg).comp natDiv
  let normal := ite (pd.comp natZero) (nm.fanout dm)
    (constant (encodePair Signed.encode Nat.bits) (encodePair Signed.encode Nat.bits) (0,1))
  refine normal.recode id (fun _ => rfl) ?_
  intro x
  simp only [Function.comp_apply,id_eq,decide_eq_true_eq]
  change encodePair Signed.encode Nat.bits (Ratio.normalized x)=Ratio.encode (mkRat x.1 x.2)
  rw [Ratio.normalized_eq]
  rfl

noncomputable def ratNum : PolyProgram Ratio.encode Signed.encode Rat.num :=
  (fst Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def ratDen : PolyProgram Ratio.encode Nat.bits Rat.den :=
  (snd Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def ratNeg : PolyProgram Ratio.encode Ratio.encode Neg.neg := by
  refine (((ratNum.comp intNeg).fanout ratDen)).recode id (fun _ => rfl) ?_
  intro q
  simp only [Function.comp_apply,id_eq,Ratio.encode,Ratio.parts,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den]
noncomputable def ratOfInt : PolyProgram Signed.encode Ratio.encode Int.cast :=
  (((identity Signed.encode).fanout (constant Signed.encode Nat.bits 1)).comp mkRational).congr _ (fun z => by simp [Rat.mkRat_eq_div])
noncomputable def ratOfNat : PolyProgram Nat.bits Ratio.encode Nat.cast :=
  (intOfNat.comp ratOfInt).congr _ (fun n => by simp)
noncomputable def ratMul : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1*x.2) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let pn := ((px.comp ratNum).fanout (py.comp ratNum)).comp intMul
  let pd := ((px.comp ratDen).fanout (py.comp ratDen)).comp natMul
  exact ((pn.fanout pd).comp mkRational).congr _ (fun x => (Rat.mul_def' x.1 x.2).symm)
noncomputable def ratAdd : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1+x.2) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let pnx := ((px.comp ratNum).fanout ((py.comp ratDen).comp intOfNat)).comp intMul
  let pny := ((py.comp ratNum).fanout ((px.comp ratDen).comp intOfNat)).comp intMul
  let pn := (pnx.fanout pny).comp intAdd
  let pd := ((px.comp ratDen).fanout (py.comp ratDen)).comp natMul
  exact ((pn.fanout pd).comp mkRational).congr _ (fun x => (Rat.add_def' x.1 x.2).symm)
noncomputable def ratSub : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1-x.2) :=
  ((ratNeg.second Ratio.encode).comp ratAdd).congr _ (fun x => (sub_eq_add_neg x.1 x.2).symm)
noncomputable def ratInv : PolyProgram Ratio.encode Ratio.encode Inv.inv :=
  (((((ratNum.comp intSign).fanout ratDen).comp intFromParts).fanout (ratNum.comp intAbs)).comp mkRational).congr _ (fun q => (Ratio.inv_eq q).symm)
noncomputable def ratDiv : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1/x.2) :=
  ((ratInv.second Ratio.encode).comp ratMul).congr _ (fun x => (div_eq_mul_inv x.1 x.2).symm)
noncomputable def ratLT : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1 < x.2)) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let lhs := ((px.comp ratNum).fanout ((py.comp ratDen).comp intOfNat)).comp intMul
  let rhs := ((py.comp ratNum).fanout ((px.comp ratDen).comp intOfNat)).comp intMul
  refine ((lhs.fanout rhs).comp intLT).congr _ ?_
  intro x
  simp only [Function.comp_apply]
  simp only [← Rat.lt_iff]
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.GaussianKernel -/
section
namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def residual {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1)) :
    Fin r → Fin n → ℚ :=
  fun i j => A i.succ (p.succAbove j) - A 0 (p.succAbove j)/A 0 p*A i.succ p

def lift {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (z : Fin n → ℚ) : Fin (n+1) → ℚ :=
  p.insertNth (-(∑ j, A 0 (p.succAbove j)/A 0 p*z j)) z

theorem lift_nonzero {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (z : Fin n → ℚ) (hz : ∃ j, z j ≠ 0) : ∃ j, lift A p z j ≠ 0 := by
  obtain ⟨j,hj⟩ := hz
  exact ⟨p.succAbove j, by simpa only [lift,Fin.insertNth_apply_succAbove] using hj⟩

theorem lift_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (hp : A 0 p ≠ 0) (z : Fin n → ℚ)
    (hz : ∀ i, ∑ j, residual A p i j*z j=0) :
    ∀ i, ∑ j, A i j*lift A p z j=0 := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Fin.sum_univ_succAbove _ p]
    simp only [lift,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,mul_neg]
    have hs : A 0 p*(∑ j, A 0 (p.succAbove j)/A 0 p*z j)=
        ∑ j, A 0 (p.succAbove j)*z j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      field_simp
    rw [hs,neg_add_cancel]
  · rw [Fin.sum_univ_succAbove _ p]
    simp only [lift,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    have hh := hz i
    simp only [residual,sub_mul,sum_sub_distrib] at hh
    have he : (∑ j, A 0 (p.succAbove j)/A 0 p*A i.succ p*z j)=
        A i.succ p*(∑ j, A 0 (p.succAbove j)/A 0 p*z j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    rw [he] at hh
    linarith

def kernel : (r n : ℕ) → (Fin r → Fin n → ℚ) → Fin n → ℚ
  | 0, _, _ => fun j => if j.val=0 then 1 else 0
  | _+1, 0, _ => Fin.elim0
  | r+1, n+1, A =>
    if h : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty then
      let p := (univ.filter (fun j => A 0 j ≠ 0)).min' h
      lift A p (kernel r n (residual A p))
    else kernel r (n+1) (fun i j => A i.succ j)

theorem kernel_spec (r n : ℕ) (A : Fin r → Fin n → ℚ) (hn : r < n) :
    (∃ j, kernel r n A j ≠ 0) ∧ (∀ i, ∑ j, A i j*kernel r n A j=0) := by
  induction r generalizing n with
  | zero =>
    have hn0 : 0 < n := hn
    refine ⟨⟨⟨0,hn0⟩,?_⟩,fun i => Fin.elim0 i⟩
    simp only [kernel,ite_true,ne_eq,one_ne_zero,not_false_eq_true]
  | succ r ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hh : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty
      · let p := (univ.filter (fun j => A 0 j ≠ 0)).min' hh
        have hp : A 0 p ≠ 0 := (mem_filter.mp (min'_mem _ hh)).2
        have hi := ih n (residual A p) (by omega)
        change (∃ j, (if h : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty then
            lift A ((univ.filter (fun j => A 0 j ≠ 0)).min' h)
              (kernel r n (residual A ((univ.filter (fun j => A 0 j ≠ 0)).min' h)))
            else kernel r (n+1) (fun i j => A i.succ j)) j ≠ 0) ∧ _
        simp only [kernel,dif_pos hh]
        exact ⟨lift_nonzero A p _ hi.1,lift_kernel A p hp _ hi.2⟩
      · have hzero : ∀ j, A 0 j=0 := by
          intro j
          by_contra hj
          exact hh ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
        have hi := ih (n+1) (fun i j => A i.succ j) (by omega)
        have he : kernel (r+1) (n+1) A=kernel r (n+1) (fun i j => A i.succ j) := by
          rw [kernel,dif_neg hh]
        rw [he]
        refine ⟨hi.1,?_⟩
        intro i
        refine Fin.cases ?_ (fun i => hi.2 i) i
        simp only [hzero,zero_mul,sum_const_zero]

end MetricKMedian.Gaussian

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.GaussianCircuit -/
section
namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def IsCircuit {r n : ℕ} (A : Fin r → Fin n → ℚ) (z : Fin n → ℚ) : Prop :=
  ∀ v : Fin n → ℚ, (∀ j, z j=0 → v j=0) → (∀ i, ∑ j, A i j*v j=0) →
    ∃ t : ℚ, ∀ j, v j=t*z j

theorem lift_eq_of_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (v : Fin (n+1) → ℚ)
    (h0 : ∑ j, A 0 j*v j=0) :
    v=lift A p (fun j => v (p.succAbove j)) := by
  have he : v p= -(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j)) := by
    rw [Fin.sum_univ_succAbove _ p] at h0
    have hs : A 0 p*(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j))=
        ∑ j, A 0 (p.succAbove j)*v (p.succAbove j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      field_simp
    apply (mul_left_cancel₀ hp)
    rw [mul_neg,hs]
    linarith
  funext j
  by_cases hj : j=p
  · subst j
    simpa only [lift,Fin.insertNth_apply_same] using he
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [lift,Fin.insertNth_apply_succAbove]

theorem residual_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (v : Fin (n+1) → ℚ)
    (hv : ∀ i, ∑ j, A i j*v j=0) :
    ∀ i, ∑ j, residual A p i j*v (p.succAbove j)=0 := by
  have he := lift_eq_of_kernel A p hp v (hv 0)
  intro i
  have hi := hv i.succ
  rw [Fin.sum_univ_succAbove _ p] at hi
  have hep := congrFun he p
  simp only [lift,Fin.insertNth_apply_same] at hep
  rw [hep] at hi
  simp only [residual,sub_mul,sum_sub_distrib]
  have hs : (∑ j, A 0 (p.succAbove j)/A 0 p*A i.succ p*v (p.succAbove j))=
      A i.succ p*(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [hs]
  linarith

theorem lift_smul {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (z : Fin n → ℚ) (t : ℚ) :
    lift A p (fun j => t*z j)=fun j => t*lift A p z j := by
  funext j
  by_cases hj : j=p
  · subst j
    simp only [lift,Fin.insertNth_apply_same]
    rw [mul_neg, mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [lift,Fin.insertNth_apply_succAbove]

theorem lift_circuit {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (z : Fin n → ℚ)
    (hz : IsCircuit (residual A p) z) : IsCircuit A (lift A p z) := by
  intro v hs hv
  have hsub : ∀ j, z j=0 → v (p.succAbove j)=0 := by
    intro j hj
    apply hs
    simpa only [lift,Fin.insertNth_apply_succAbove] using hj
  obtain ⟨t,ht⟩ := hz (fun j => v (p.succAbove j)) hsub (residual_kernel A p hp v hv)
  refine ⟨t,?_⟩
  have he := lift_eq_of_kernel A p hp v (hv 0)
  rw [show (fun j => v (p.succAbove j))=(fun j => t*z j) from funext ht,lift_smul] at he
  exact congrFun he

theorem kernel_circuit (r n : ℕ) (A : Fin r → Fin n → ℚ) (hn : r < n) :
    (∃ j, kernel r n A j=1) ∧ IsCircuit A (kernel r n A) := by
  induction r generalizing n with
  | zero =>
    let j0 : Fin n := ⟨0,hn⟩
    refine ⟨⟨j0,by simp only [kernel,j0,ite_true]⟩,?_⟩
    intro v hs _
    refine ⟨v j0,?_⟩
    intro j
    by_cases hj : j.val=0
    · have he : j=j0 := Fin.ext hj
      subst j
      simp only [kernel,j0,ite_true,mul_one]
    · have hh := hs j (by simp only [kernel,if_neg hj])
      simp only [kernel,if_neg hj,mul_zero,hh]
  | succ r ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hh : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty
      · let p := (univ.filter (fun j => A 0 j ≠ 0)).min' hh
        have hp : A 0 p ≠ 0 := (mem_filter.mp (min'_mem _ hh)).2
        obtain ⟨⟨j,hj⟩,hc⟩ := ih n (residual A p) (by omega)
        have he : kernel (r+1) (n+1) A=lift A p (kernel r n (residual A p)) := by
          rw [kernel,dif_pos hh]
        rw [he]
        refine ⟨⟨p.succAbove j,?_⟩,lift_circuit A p hp _ hc⟩
        simpa only [lift,Fin.insertNth_apply_succAbove] using hj
      · have hi := ih (n+1) (fun i j => A i.succ j) (by omega)
        have he : kernel (r+1) (n+1) A=kernel r (n+1) (fun i j => A i.succ j) := by
          rw [kernel,dif_neg hh]
        rw [he]
        refine ⟨hi.1,?_⟩
        intro v hs hv
        exact hi.2 v hs (fun i => hv i.succ)

end MetricKMedian.Gaussian

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.GramDependence -/
section
namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

theorem gram_det_ne_zero (A : Matrix R C ℤ)
    (hi : LinearIndependent ℚ (fun c => fun r => (A r c:ℚ))) :
    (A.transpose*A).det ≠ 0 := by
  intro hz
  obtain ⟨v,hv,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have hzero : A*ᵥv=0 := by
    have hh := congrArg (dotProduct v) hker
    rw [← mulVec_mulVec,dotProduct_mulVec,dotProduct_zero,vecMul_transpose,
      dotProduct_self_eq_zero] at hh
    exact hh
  have hlin : Function.Injective ((fun r c => (A r c:ℚ)) *ᵥ ·) :=
    Matrix.mulVec_injective_iff.mpr hi
  have hcast : (fun r c => (A r c:ℚ))*ᵥ(fun c => (v c:ℚ))=0 := by
    ext r
    have hh := congrFun hzero r
    change (∑ c, A r c*v c)=0 at hh
    change (∑ c, (A r c:ℚ)*(v c:ℚ))=0
    exact_mod_cast hh
  have hvQ := hlin (hcast.trans (mulVec_zero _).symm)
  apply hv
  ext c
  have hh := congrFun hvQ c
  change (v c:ℚ)=0 at hh
  change v c=0
  exact_mod_cast hh

theorem gram_span_relation (A : Matrix R C ℤ) (w : R → ℤ)
    (hi : LinearIndependent ℚ (fun c => fun r => (A r c:ℚ)))
    (hc : (fun r => (w r:ℚ)) ∈ Submodule.span ℚ (Set.range (fun c => fun r => (A r c:ℚ)))) :
    let B := A.transpose*A
    let z := B.cramer (A.transpose*ᵥw)
    ∀ r, (A*ᵥz) r=B.det*w r := by
  let AQ : Matrix R C ℚ := fun r c => A r c
  have hc' : (fun r => (w r:ℚ)) ∈ LinearMap.range AQ.mulVecLin := by
    rwa [Matrix.range_mulVecLin]
  obtain ⟨x,hx⟩ := hc'
  change AQ*ᵥx=(fun r => (w r:ℚ)) at hx
  let B := A.transpose*A
  let z := B.cramer (A.transpose*ᵥw)
  have hz := Matrix.mulVec_cramer B (A.transpose*ᵥw)
  have hdet : B.det ≠ 0 := gram_det_ne_zero A hi
  have hB : Function.Injective ((fun c d => (B c d:ℚ))*ᵥ ·) := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    change IsUnit (((Int.castRingHom ℚ).mapMatrix B).det)
    rw [← RingHom.map_det (Int.castRingHom ℚ)]
    apply isUnit_iff_ne_zero.mpr
    change (B.det:ℚ) ≠ 0
    exact_mod_cast hdet
  have hBcast : (fun c d => (B c d:ℚ))=AQ.transpose*AQ := by
    exact Matrix.map_mul (L:=A.transpose) (M:=A) (f:=Int.castRingHom ℚ)
  have hzQ : (AQ.transpose*AQ)*ᵥ(fun c => (z c:ℚ))=(B.det:ℚ) •
      (AQ.transpose*ᵥ(fun r => (w r:ℚ))) := by
    rw [← hBcast]
    ext c
    have hh := congrFun hz c
    simp only [mulVec,dotProduct,Pi.smul_apply,smul_eq_mul] at hh ⊢
    change (∑ d, (B c d:ℚ)*(z d:ℚ))=(B.det:ℚ)*∑ r, (A r c:ℚ)*(w r:ℚ)
    change (∑ d, B c d*z d)=B.det*∑ r, A r c*w r at hh
    exact_mod_cast hh
  have he : (fun c => (z c:ℚ))=(B.det:ℚ) • x := by
    apply hB
    change ((fun c d => (B c d:ℚ))*ᵥ(fun c => (z c:ℚ))) =
      (fun c d => (B c d:ℚ))*ᵥ((B.det:ℚ) • x)
    rw [hBcast,hzQ,mulVec_smul,← mulVec_mulVec,hx]
  change ∀ r, (A*ᵥz) r=B.det*w r
  intro r
  have heq : (AQ*ᵥ(fun c => (z c:ℚ))) r=(B.det:ℚ)*(w r:ℚ) := by
    rw [he,mulVec_smul,hx]
    rfl
  simp only [mulVec,dotProduct,AQ] at heq ⊢
  exact_mod_cast heq

end MetricKMedian.Compression

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.GramBounds -/
section
namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix
variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
                                                                      
theorem gram_entry_bound (A : Matrix R C ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (c d : C) :
    |(A.transpose*A) c d| ≤ (Fintype.card R:ℤ)*M^2 := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ r, |A r c*A r d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R, M^2 := sum_le_sum (fun r _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hA r c) (hA r d) (abs_nonneg _) hM)
    _ = _ := by simp

omit [Fintype C] [DecidableEq C] in
theorem gram_rhs_bound (A : Matrix R C ℤ) (w : R → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (hw : ∀ r, |w r| ≤ M) (c : C) :
    |(A.transpose*ᵥw) c| ≤ (Fintype.card R:ℤ)*M^2 := by
  change |∑ r, A r c*w r| ≤ _
  calc
    _ ≤ ∑ r, |A r c*w r| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R, M^2 := sum_le_sum (fun r _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hA r c) (hw r) (abs_nonneg _) hM)
    _ = _ := by simp

theorem gram_det_bound (A : Matrix R C ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) :
    |(A.transpose*A).det| ≤ (Nat.factorial (Fintype.card C):ℤ)*
      ((Fintype.card R:ℤ)*M^2)^(Fintype.card C) := by
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) (gram_entry_bound A M hM hA))

theorem gram_cramer_bound (A : Matrix R C ℤ) (w : R → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (hw : ∀ r, |w r| ≤ M) (c : C) :
    |((A.transpose*A).cramer (A.transpose*ᵥw)) c| ≤ (Nat.factorial (Fintype.card C):ℤ)*
      ((Fintype.card R:ℤ)*M^2)^(Fintype.card C) := by
  rw [Matrix.cramer_apply]
  have hentry : ∀ i j, |((A.transpose*A).updateCol c (A.transpose*ᵥw)) i j| ≤
      (Fintype.card R:ℤ)*M^2 := by
    intro i j
    by_cases hj : j=c
    · subst j
      simpa using gram_rhs_bound A w M hM hA hw i
    · simpa [Matrix.updateCol_apply,hj] using gram_entry_bound A M hM hA i j
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) hentry)

end MetricKMedian.Compression

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.IntegerCoefficientBounds -/
section
namespace OAI

namespace MetricKMedian.Compression

theorem gram_coefficient_bit_bound (r n L : ℕ) (hn : n ≤ r) :
    (n.factorial:ℤ)*((r:ℤ)*((2:ℤ)^L)^2)^n ≤ (2:ℤ)^(2*r*(r+L)) := by
  have hnr : n ≤ 2^r := hn.trans Nat.lt_two_pow_self.le
  have hf : n.factorial ≤ 2^(r*r) := by
    calc
      _ ≤ n^n := Nat.factorial_le_pow n
      _ ≤ (2^r)^n := Nat.pow_le_pow_left hnr n
      _ = 2^(r*n) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left r hn)
  have hfZ : (n.factorial:ℤ) ≤ 2^(r*r) := by exact_mod_cast hf
  have hrZ : (r:ℤ) ≤ 2^r := by exact_mod_cast (Nat.lt_two_pow_self (n:=r)).le
  have hb : (r:ℤ)*((2:ℤ)^L)^2 ≤ 2^(r+2*L) := by
    calc
      _ ≤ 2^r*((2:ℤ)^L)^2 := mul_le_mul_of_nonneg_right hrZ (sq_nonneg _)
      _ = _ := by rw [pow_add,Nat.mul_comm 2 L,pow_mul]
  have hbn : ((r:ℤ)*((2:ℤ)^L)^2)^n ≤ 2^((r+2*L)*r) := by
    calc
      _ ≤ ((2:ℤ)^(r+2*L))^n := pow_le_pow_left₀ (by positivity) hb n
      _ = 2^((r+2*L)*n) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hn)
  calc
    _ ≤ 2^(r*r)*(2:ℤ)^((r+2*L)*r) :=
      mul_le_mul hfZ hbn (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

end MetricKMedian.Compression

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.DependentIntegerKernel -/
section
namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

theorem small_integer_dependence_of_dependent {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hdep : ¬ LinearIndependent ℚ (fun i r => (V r i:ℚ))) :
    ∃ (K : Type) (inst : Fintype K), letI := inst;
      ∃ (a : K → Ω) (z : K → ℤ), Function.Injective a ∧
        Fintype.card K ≤ Fintype.card R+1 ∧ (∃ k, z k ≠ 0) ∧
        (∀ k, |z k| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
        ∀ r, ∑ k, z k*V r (a k)=0 := by
  classical
  let v : Ω → R → ℚ := fun i r => V r i
  obtain ⟨κ,a,ha,hspan,hi⟩ := exists_linearIndependent' ℚ v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ ≤ Fintype.card R := by
    simpa using hi.fintype_card_le_finrank
  have hns : ¬ Function.Surjective a := by
    intro hs
    apply hdep
    let e := Equiv.ofBijective a ⟨ha,hs⟩
    have hh := hi.comp e.symm e.symm.injective
    have he : (v ∘ a) ∘ e.symm=v := by
      funext i
      change v (e (e.symm i))=v i
      rw [e.apply_symm_apply]
    rw [he] at hh
    exact hh
  simp only [Function.Surjective,not_forall,not_exists] at hns
  obtain ⟨w,hw⟩ := hns
  let A : Matrix R κ ℤ := fun r c => V r (a c)
  let wv : R → ℤ := fun r => V r w
  let B := A.transpose*A
  let D := B.det
  let b := B.cramer (A.transpose*ᵥwv)
  have hAi : LinearIndependent ℚ (fun c r => (A r c:ℚ)) := hi
  have hwm : (fun r => (wv r:ℚ)) ∈ Submodule.span ℚ (Set.range (fun c r => (A r c:ℚ))) := by
    change v w ∈ Submodule.span ℚ (Set.range (v ∘ a))
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self w)
  have hD : D ≠ 0 := gram_det_ne_zero A hAi
  have heq : ∀ r, (A*ᵥb) r=D*wv r := gram_span_relation A wv hAi hwm
  have hbnd := gram_coefficient_bit_bound (Fintype.card R) (Fintype.card κ) L hcard
  have hAb : ∀ r c, |A r c| ≤ (2:ℤ)^L := fun r c => hV r (a c)
  have hwv : ∀ r, |wv r| ≤ (2:ℤ)^L := fun r => hV r w
  have hDb : |D| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L)) :=
    (gram_det_bound A _ (by positivity) hAb).trans hbnd
  have hbb : ∀ c, |b c| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L)) :=
    fun c => (gram_cramer_bound A wv _ (by positivity) hAb hwv c).trans hbnd
  let a' : Option κ → Ω := fun k => k.elim w a
  let z : Option κ → ℤ := fun k => k.elim D (fun c => -b c)
  refine ⟨Option κ,inferInstance,a',z,?_,?_,⟨none,hD⟩,?_,?_⟩
  · intro c d he
    cases c with
    | none =>
      cases d with
      | none => rfl
      | some d => exact False.elim (hw d he.symm)
    | some c =>
      cases d with
      | none => exact False.elim (hw c he)
      | some d => exact congrArg some (ha he)
  · simp only [Fintype.card_option]
    omega
  · intro k
    cases k with
    | none => exact hDb
    | some c => simpa only [z,Option.elim_some,abs_neg] using hbb c
  · intro r
    rw [Fintype.sum_option]
    change D*wv r+(∑ c, (-b c)*A r c)=0
    have hh := heq r
    change (∑ c, A r c*b c)=D*wv r at hh
    simp only [neg_mul,sum_neg_distrib,mul_comm (b _) (A _ _)]
    rw [hh]
    ring

theorem full_integer_kernel_of_dependent {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hdep : ¬ LinearIndependent ℚ (fun i r => (V r i:ℚ))) :
    ∃ z : Ω → ℤ, (∃ i, z i ≠ 0) ∧
      (∀ i, |z i| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
      ∀ r, ∑ i, z i*V r i=0 := by
  classical
  obtain ⟨K,inst,a,z,ha,_,hne,hbound,hker⟩ := small_integer_dependence_of_dependent V L hV hdep
  let zz : Ω → ℤ := fun i => ∑ k, if a k=i then z k else 0
  have hzval : ∀ k, zz (a k)=z k := by
    intro k
    simp only [zz,ha.eq_iff]
    simpa only [mem_univ,ite_true] using sum_ite_eq' univ k z
  have hzout : ∀ i, (¬∃ k, a k=i) → zz i=0 := by
    intro i hi
    apply sum_eq_zero
    intro k _
    exact if_neg (fun hk => hi ⟨k,hk⟩)
  refine ⟨zz,?_,?_,?_⟩
  · obtain ⟨k,hk⟩ := hne
    exact ⟨a k,by rwa [hzval]⟩
  · intro i
    by_cases hi : ∃ k, a k=i
    · obtain ⟨k,rfl⟩ := hi
      rw [hzval]
      exact hbound k
    · rw [hzout i hi,abs_zero]
      positivity
  · intro r
    change (∑ i, (∑ k, if a k=i then z k else 0)*V r i)=0
    simp only [sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    simpa using hker r

end MetricKMedian.Compression

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.CircuitBitBound -/
section
namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem circuit_integer_ratio {r n : ℕ} (V : Fin r → Fin n → ℤ)
    (z : Fin n → ℚ) (L : ℕ) (hV : ∀ i j, |V i j| ≤ (2:ℤ)^L)
    (hz : ∀ i, ∑ j, (V i j:ℚ)*z j=0)
    (hc : IsCircuit (fun i j => (V i j:ℚ)) z) (w : Fin n) (hw : z w=1) :
    ∃ U : Fin n → ℤ, U w ≠ 0 ∧
      (∀ j, |U j| ≤ (2:ℤ)^(2*r*(r+L))) ∧
      ∀ j, z j=(U j:ℚ)/(U w:ℚ) := by
  classical
  let S := univ.filter (fun j => z j ≠ 0)
  have hwS : w ∈ S := by simp only [S,mem_filter,mem_univ,true_and,hw,ne_eq,one_ne_zero,not_false_eq_true]
  have hdep : ¬ LinearIndependent ℚ (fun j : ↥S => fun i => (V i j.val:ℚ)) := by
    intro hi
    have hsum : ∑ j : ↥S, z j.val • (fun i => (V i j.val:ℚ))=0 := by
      funext i
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
      rw [sum_coe_sort S (fun j => z j*(V i j:ℚ))]
      have he : (∑ j ∈ S, z j*(V i j:ℚ))=∑ j, z j*(V i j:ℚ) := by
        apply sum_subset (subset_univ _)
        intro j _ hj
        have he : z j=0 := by simpa only [S,mem_filter,mem_univ,true_and,not_not] using hj
        rw [he,zero_mul]
      rw [he]
      simpa only [mul_comm] using hz i
    have hh := (Fintype.linearIndependent_iff.mp hi) (fun j => z j.val) hsum ⟨w,hwS⟩
    rw [hw] at hh
    exact one_ne_zero hh
  obtain ⟨u,hune,hb,hker⟩ := Compression.full_integer_kernel_of_dependent
    (fun i (j : ↥S) => V i j.val) L (fun i j => hV i j.val) hdep
  let U : Fin n → ℤ := fun j => if h : j ∈ S then u ⟨j,h⟩ else 0
  have hUval : ∀ j : ↥S, U j.val=u j := by intro j; simp only [U,dif_pos j.property]
  have hUne : ∃ j, U j ≠ 0 := by
    obtain ⟨j,hj⟩ := hune
    exact ⟨j.val,by rwa [hUval]⟩
  have hUz : ∀ j, z j=0 → U j=0 := by
    intro j hj
    have hn : j ∉ S := by simp only [S,mem_filter,mem_univ,true_and,hj,ne_eq,not_true_eq_false,not_false_eq_true]
    exact dif_neg hn
  have hUker : ∀ i, ∑ j, (V i j:ℚ)*(U j:ℚ)=0 := by
    intro i
    have hh : (∑ j, U j*V i j)=∑ j : ↥S, u j*V i j.val := by
      calc
        _ = ∑ j ∈ S, U j*V i j := by
          symm
          apply sum_subset (subset_univ _)
          intro j _ hj
          simp only [U,dif_neg hj,zero_mul]
        _ = _ := by rw [← sum_coe_sort]; exact sum_congr rfl (fun j _ => by rw [hUval])
    have hh' := hh.trans (hker i)
    have hcast : (∑ j, (U j:ℚ)*(V i j:ℚ))=0 := by exact_mod_cast hh'
    simpa only [mul_comm] using hcast
  obtain ⟨t,ht⟩ := hc (fun j => (U j:ℚ)) (by intro j hj; exact_mod_cast hUz j hj) hUker
  have htw : (U w:ℚ)=t := by simpa only [hw,mul_one] using ht w
  have htn : t ≠ 0 := by
    intro ht0
    obtain ⟨j,hj⟩ := hUne
    have hh := ht j
    rw [ht0,zero_mul] at hh
    exact hj (by exact_mod_cast hh)
  have hUw : U w ≠ 0 := by intro hn; simp only [hn,Int.cast_zero] at htw; exact htn htw.symm
  refine ⟨U,hUw,?_,?_⟩
  · intro j
    by_cases hj : j ∈ S
    · rw [show U j=u ⟨j,hj⟩ from dif_pos hj]
      simpa only [Fintype.card_fin] using hb ⟨j,hj⟩
    · rw [show U j=0 from dif_neg hj,abs_zero]; positivity
  · intro j
    rw [htw]
    apply (eq_div_iff htn).mpr
    rw [ht j]
    ring

theorem ratio_num_den_bound (a b : ℤ) (hb : b ≠ 0) (H : ℤ)
    (ha : |a| ≤ H) (hbH : |b| ≤ H) :
    |((a:ℚ)/(b:ℚ)).num| ≤ H ∧ (((a:ℚ)/(b:ℚ)).den:ℤ) ≤ H := by
  let q := (a:ℚ)/(b:ℚ)
  obtain ⟨c,hcA,hcB⟩ := Rat.num_den_mk hb (q := q) (by exact (Rat.divInt_eq_div a b).symm)
  have hc : c ≠ 0 := by intro hz; rw [hz,zero_mul] at hcB; exact hb hcB
  have hc1 : (1:ℤ) ≤ |c| := by
    have ha := abs_pos.mpr hc
    omega
  have hnum : |q.num| ≤ |a| := by
    rw [hcA,abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (abs_nonneg q.num)
  have hden : (q.den:ℤ) ≤ |b| := by
    rw [hcB,abs_mul,abs_of_nonneg (by positivity : (0:ℤ) ≤ q.den)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (Int.natCast_nonneg q.den)
  exact ⟨hnum.trans ha,hden.trans hbH⟩

theorem integer_input_kernel_bounds (r n L : ℕ) (V : Fin r → Fin n → ℤ)
    (hn : r < n) (hV : ∀ i j, |V i j| ≤ (2:ℤ)^L) :
    let z := kernel r n (fun i j => (V i j:ℚ))
    ∀ j, |(z j).num| ≤ (2:ℤ)^(2*r*(r+L)) ∧
      ((z j).den:ℤ) ≤ (2:ℤ)^(2*r*(r+L)) := by
  dsimp only
  obtain ⟨⟨w,hw⟩,hc⟩ := kernel_circuit r n (fun i j => (V i j:ℚ)) hn
  have hk := (kernel_spec r n (fun i j => (V i j:ℚ)) hn).2
  obtain ⟨U,hUw,hU,hz⟩ := circuit_integer_ratio V _ L hV hk hc w hw
  intro j
  rw [hz j]
  exact ratio_num_den_bound (U j) (U w) hUw _ (hU j) (hU w)

end MetricKMedian.Gaussian

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.RationalOperationHeight -/
section
namespace OAI


                                               
section
namespace MetricKMedian.Binary
open Finset

def HasHeight (q : ℚ) (L : ℕ) : Prop := |q.num| ≤ (2:ℤ)^L ∧ (q.den:ℤ) ≤ (2:ℤ)^L

namespace HasHeight
variable {q r : ℚ} {L M : ℕ}

 theorem mono (h : HasHeight q L) (hLM : L≤M) : HasHeight q M :=
  ⟨h.1.trans (pow_le_pow_right₀ (by norm_num) hLM),h.2.trans (pow_le_pow_right₀ (by norm_num) hLM)⟩

 theorem zero (L : ℕ) : HasHeight 0 L := by
  constructor
  · simp
  · simp only [Rat.den_zero,Int.natCast_one]
    exact one_le_pow₀ (by norm_num)

 theorem one (L : ℕ) : HasHeight 1 L := by
  constructor <;> simp only [Rat.num_one,Rat.den_one,abs_one,Int.natCast_one] <;>
    exact one_le_pow₀ (by norm_num)

 theorem neg (h : HasHeight q L) : HasHeight (-q) L := by
  simpa only [HasHeight,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den,abs_neg] using h

 theorem mul (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q*r) (L+M) := by
  have hdq : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdr : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hh := Gaussian.ratio_num_den_bound (q.num*r.num) ((q.den:ℤ)*r.den) (mul_ne_zero hdq hdr)
    ((2:ℤ)^(L+M)) (by
      rw [abs_mul,pow_add]
      exact mul_le_mul hq.1 hr.1 (abs_nonneg _) (by positivity)) (by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _),pow_add]
      exact mul_le_mul hq.2 hr.2 (by positivity) (by positivity))
  have he : ((q.num*r.num:ℤ):ℚ)/(((q.den:ℤ)*r.den:ℤ):ℚ)=q*r := by
    push_cast
    rw [mul_div_mul_comm,Rat.num_div_den,Rat.num_div_den]
  rwa [he] at hh

 theorem inv (hq : HasHeight q L) : HasHeight q⁻¹ L := by
  by_cases hq0 : q=0
  · rw [hq0,inv_zero]
    exact zero L
  have hqn : q.num ≠ 0 := by
    intro h
    apply hq0
    rw [← Rat.num_div_den q,h,Int.cast_zero,zero_div]
  have hh := Gaussian.ratio_num_den_bound (q.den:ℤ) q.num hqn ((2:ℤ)^L)
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using hq.2) hq.1
  have he : ((q.den:ℤ):ℚ)/(q.num:ℚ)=q⁻¹ := by
    conv_rhs => rw [← Rat.num_div_den q]
    simp only [inv_div,Int.cast_natCast]
  rwa [he] at hh

 theorem div (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q/r) (L+M) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv

 theorem add (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q+r) (L+M+1) := by
  have hdq : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdr : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hterm₁ : |q.num*(r.den:ℤ)| ≤ (2:ℤ)^(L+M) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),pow_add]
    exact mul_le_mul hq.1 hr.2 (by positivity) (by positivity)
  have hterm₂ : |r.num*(q.den:ℤ)| ≤ (2:ℤ)^(L+M) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Nat.add_comm L M,pow_add]
    exact mul_le_mul hr.1 hq.2 (by positivity) (by positivity)
  have hh := Gaussian.ratio_num_den_bound (q.num*r.den+r.num*q.den) ((q.den:ℤ)*r.den)
    (mul_ne_zero hdq hdr) ((2:ℤ)^(L+M+1)) (by
      have hab := abs_add_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ))
      rw [pow_succ]
      linarith) (by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _)]
      have hb : (q.den:ℤ)*r.den ≤ (2:ℤ)^(L+M) := by
        rw [pow_add]
        exact mul_le_mul hq.2 hr.2 (by positivity) (by positivity)
      exact hb.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
  have he : ((q.num*r.den+r.num*q.den:ℤ):ℚ)/(((q.den:ℤ)*r.den:ℤ):ℚ)=q+r := by
    push_cast
    rw [add_div, mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr r.den_ne_zero),
      mul_comm (r.num:ℚ) (q.den:ℚ),mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr q.den_ne_zero),
      Rat.num_div_den,Rat.num_div_den]
  rwa [he] at hh

 theorem sub (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q-r) (L+M+1) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

 theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i∈s, HasHeight (f i) L) :
    HasHeight (∑ i∈s, f i) (s.card*(L+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty,card_empty,zero_mul] using zero 0
  | @insert a s ha ih =>
      rw [sum_insert ha,card_insert_of_notMem ha]
      have hs := ih (fun i hi => h i (mem_insert_of_mem hi))
      have hh := (h a (mem_insert_self _ _)).add hs
      convert hh using 1
      ring

 theorem partialSum {n : ℕ} (f : Fin n → ℚ) (s : Finset (Fin n))
    (h : ∀ i, HasHeight (f i) L) : HasHeight (∑ i∈s, f i) (n*(L+1)) := by
  have hh := sum s f (fun i _ => h i)
  apply hh.mono
  exact Nat.mul_le_mul_right _ ((card_le_card (subset_univ s)).trans_eq (card_fin n))

end HasHeight
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryRationalHeight -/
section
namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Polynomial
namespace NatBinary
 theorem length_le_height {n L : ℕ} (h : n ≤ 2^L) : n.bits.length ≤ L+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hp : 0<2^L := pow_pos (by decide) _
  rw [pow_succ]
  omega
 theorem le_two_pow_length (n : ℕ) : n ≤ 2^n.bits.length := by
  simpa only [Nat.size_eq_bits_len] using (Nat.lt_size_self n).le
end NatBinary

namespace Signed
 theorem encode_length (z : ℤ) : (encode z).length=3+z.natAbs.bits.length := by
  simp only [encode,parts,encodePair_length,encodeBool,List.length_singleton]

 theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh := encodePair_injective encodeBool_injective (fun n m he => by
    have hg := congrArg Word.value he
    simpa only [Word.value_bits] using hg) h
  have hx := congrArg (fun x : Bool × ℕ => value x.1 x.2) hh
  simpa only [parts,value_parts] using hx
end Signed
namespace Ratio
 theorem encode_length (q : ℚ) : (encode q).length=7+2*q.num.natAbs.bits.length+q.den.bits.length := by
  simp only [encode,parts,encodePair_length,Signed.encode_length]
  omega
 theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh := encodePair_injective Signed.encode_injective (fun n m he => by
    have hg := congrArg Word.value he
    simpa only [Word.value_bits] using hg) h
  have hn := congrArg Prod.fst hh
  have hd := congrArg Prod.snd hh
  exact Rat.ext hn hd
 theorem height_length (q : ℚ) : HasHeight q (encode q).length := by
  have hn := NatBinary.le_two_pow_length q.num.natAbs
  have hd := NatBinary.le_two_pow_length q.den
  have hlen := encode_length q
  have hnb : q.num.natAbs.bits.length ≤ (encode q).length := by omega
  have hdb : q.den.bits.length ≤ (encode q).length := by omega
  have hN := hn.trans (Nat.pow_le_pow_right (by decide : 1≤2) hnb)
  have hD := hd.trans (Nat.pow_le_pow_right (by decide : 1≤2) hdb)
  constructor
  · simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using (Nat.cast_le (α:=ℤ)).mpr hN
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℤ)).mpr hD
 theorem length_height {q : ℚ} {L : ℕ} (h : HasHeight q L) : (encode q).length ≤ 3*L+10 := by
  have hN : q.num.natAbs ≤ 2^L := (Nat.cast_le (α:=ℤ)).mp (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h.1)
  have hD : q.den ≤ 2^L := (Nat.cast_le (α:=ℤ)).mp (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using h.2)
  have hnb := NatBinary.length_le_height hN
  have hdb := NatBinary.length_le_height hD
  rw [encode_length]
  omega
end Ratio
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListIndices -/
section
namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α : Type}
def indexStep (x : (ℕ × List ℕ) × α) : ℕ × List ℕ := (x.1.1+1,x.1.1::x.1.2)
 theorem pushIndices (xs : List α) (n : ℕ) (bs : List ℕ) :
    xs.foldl (fun b a => indexStep (b,a)) (n,bs)=
      (n+xs.length,(List.range' n xs.length).reverse++bs) := by
  induction xs generalizing n bs with
  | nil => simp
  | cons a xs ih =>
      change xs.foldl (fun b a => indexStep (b,a)) (n+1,n::bs)=_
      rw [ih]
      simp only [List.length_cons,List.range'_succ,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1
      omega
 theorem index_partial_size (ea : α → List Bool) (xs : List α) (x : ℕ × List ℕ) (pre suf : List α)
    (he : xs=pre++suf) :
    (encodePair Nat.bits (encodeList Nat.bits) (pre.foldl (fun b a => indexStep (b,a)) x)).length ≤
      10*((encodePair (encodeList ea) (encodePair Nat.bits (encodeList Nat.bits)) (xs,x)).length+1)^2 := by
  let L := (encodePair (encodeList ea) (encodePair Nat.bits (encodeList Nat.bits)) (xs,x)).length
  have hp : pre.length ≤ L := by
    have hp : (encodeList ea pre).length ≤ (encodeList ea xs).length := by rw [he,EncodedList.append,List.length_append]; omega
    have hh := EncodedList.length_le ea pre
    simp only [L,encodePair_length]; omega
  have hn : x.1.bits.length ≤ L := by simp only [L,encodePair_length]; omega
  have hb : (encodeList Nat.bits x.2).length ≤ L := by simp only [L,encodePair_length]; omega
  have hl : pre.length.bits.length ≤ pre.length+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
  have hc := NatBinary.add_length x.1 pre.length
  have hi : ∀ q∈List.range' x.1 pre.length, q.bits.length ≤ 2*L+2 := by
    intro q hq
    have hq' : q ≤ x.1+pre.length := (List.mem_range'_1.mp hq).2.le
    have hh := (NatBinary.length_mono hq').trans hc
    omega
  have hr := EncodedList.length_bound Nat.bits (List.range' x.1 pre.length) (2*L+2) hi
  simp only [List.length_range'] at hr
  have hcount : (x.1+pre.length).bits.length ≤ 2*L+2 := by omega
  have hr' : (encodeList Nat.bits (List.range' x.1 pre.length)).length ≤ L*(4*L+5) := by
    calc
      _ ≤ pre.length*(2*(2*L+2)+1) := hr
      _ ≤ L*(2*(2*L+2)+1) := Nat.mul_le_mul_right _ hp
      _ = L*(4*L+5) := by ring
  change (encodePair Nat.bits (encodeList Nat.bits) (pre.foldl (fun b a => indexStep (b,a)) (x.1,x.2))).length ≤ _
  rw [pushIndices]
  simp only [encodePair_length,EncodedList.append,List.length_append,EncodedList.reverse_length]
  simp only [L,encodePair_length] at hcount hr' hb
  nlinarith

end ListAlgorithms
namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listIndices : PolyProgram (encodeList ea) (encodeList Nat.bits) (fun xs : List α => List.range xs.length) := by
  let eb := encodePair Nat.bits (encodeList Nat.bits)
  let acc := fst eb ea
  let n := acc.comp (fst Nat.bits (encodeList Nat.bits))
  let bs := acc.comp (snd Nat.bits (encodeList Nat.bits))
  let inc := (n.fanout (constant (encodePair eb ea) Nat.bits 1)).comp natAdd
  let push := (n.fanout bs).comp (listCons Nat.bits)
  let step : PolyProgram (encodePair eb ea) eb ListAlgorithms.indexStep :=
    (inc.fanout push).congr _ (fun _ => rfl)
  let fold := step.listFold a0 (10*(X+1)^2) (by
    intro xs x pre suf he
    simpa only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one] using ListAlgorithms.index_partial_size ea xs x pre suf he)
  let start := (identity (encodeList ea)).fanout (constant (encodeList ea) eb (0,[]))
  exact ((((start.comp fold).comp (snd Nat.bits (encodeList Nat.bits))).comp (listReverse Nat.bits 0))).congr _ (fun xs => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.pushIndices,List.append_nil,List.reverse_reverse,← List.range_eq_range'])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListIndex -/
section
namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListSplit
variable {α : Type} (ea : α → List Bool) (a0 : α)
abbrev enc : List α × (ℕ × List α) → List Bool := encodePair (encodeList ea) (encodePair Nat.bits (encodeList ea))
abbrev out : List α × List α → List Bool := encodePair (encodeList ea) (encodeList ea)
def body (x : List α × (ℕ × List α)) : (List α × List α) ⊕ (List α × (ℕ × List α)) :=
  if x.1.isEmpty || decide (x.2.1=0) then .inl (x.2.2.reverse,x.1)
  else .inr (x.1.tail,(x.2.1-1,x.1.head?.getD a0::x.2.2))
def result (x : List α × (ℕ × List α)) : List α × List α := (x.2.2.reverse++x.1.take x.2.1,x.1.drop x.2.1)
noncomputable def program : PolyProgram (enc ea) (encodeLoop (enc ea) (out ea)) (body a0) := by
  let ls := PolyProgram.fst (encodeList ea) (encodePair Nat.bits (encodeList ea))
  let ns := PolyProgram.snd (encodeList ea) (encodePair Nat.bits (encodeList ea))
  let n := ns.comp (PolyProgram.fst Nat.bits (encodeList ea))
  let bs := ns.comp (PolyProgram.snd Nat.bits (encodeList ea))
  let zero := (((ls.comp (PolyProgram.listIsEmpty ea)).fanout (n.comp PolyProgram.natZero)).comp PolyProgram.boolOr)
  let done := (((bs.comp (PolyProgram.listReverse ea a0)).fanout ls).comp (PolyProgram.injectLeft (enc ea) (out ea)))
  let pred := ((n.fanout (PolyProgram.constant (enc ea) Nat.bits 1)).comp PolyProgram.natSub)
  let push := (((ls.comp (PolyProgram.listHead ea a0)).fanout bs).comp (PolyProgram.listCons ea))
  let cont := (((ls.comp (PolyProgram.listTail ea a0)).fanout (pred.fanout push)).comp (PolyProgram.injectRight (enc ea) (out ea)))
  exact (PolyProgram.ite zero cont done).congr _ (fun _ => rfl)

 theorem run (as bs : List α) (n S : ℕ) (hsize : (enc ea (as,(n,bs))).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea) (body a0) S t (as,(n,bs)) (result (as,(n,bs))) := by
  induction as generalizing n bs with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp only [body,result,List.isEmpty_nil,Bool.true_or,List.take_nil,List.drop_nil,List.append_nil]
      rfl
  | cons a as ih =>
      cases n with
      | zero =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp only [body,result,List.isEmpty_cons,decide_true,Bool.false_or,List.take_zero,List.drop_zero,List.append_nil]
          rfl
      | succ n =>
          have hn := NatBinary.length_mono (Nat.le_succ n)
          change n.bits.length ≤ (n+1).bits.length at hn
          have hs : (enc ea (as,(n,a::bs))).length ≤ S := by
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih (a::bs) n hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have hb : body a0 (a::as,(n+1,bs))=.inr (as,(n,a::bs)) := by simp [body]
          have he : result (as,(n,a::bs))=result (a::as,(n+1,bs)) := by
            simp only [result,List.reverse_cons,List.take_succ_cons,List.drop_succ_cons,List.append_assoc,List.singleton_append]
          rw [← he]
          exact BoundedRun.step hsize hb hr

noncomputable def loop : PolyProgram (enc ea) (out ea) result :=
  (program ea a0).loop result (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea a0 x.1 x.2.2 x.2.1 (enc ea x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListSplit

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listSplitAt : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodePair (encodeList ea) (encodeList ea)) (fun x : List α × ℕ => (x.1.take x.2,x.1.drop x.2)) := by
  let ls := fst (encodeList ea) Nat.bits
  let n := snd (encodeList ea) Nat.bits
  let start := ls.fanout (n.fanout (constant (encodePair (encodeList ea) Nat.bits) (encodeList ea) []))
  exact (start.comp (ListSplit.loop ea a0)).congr _ (fun x => by simp only [Function.comp_apply,ListSplit.result,List.reverse_nil,List.nil_append])
noncomputable def listTake : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.take x.2) :=
  ((listSplitAt ea a0).comp (fst (encodeList ea) (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listDrop : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.drop x.2) :=
  ((listSplitAt ea a0).comp (snd (encodeList ea) (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listGetD : PolyProgram (encodePair (encodeList ea) Nat.bits)
    ea (fun x : List α × ℕ => x.1[x.2]?.getD a0) := by
  exact ((listDrop ea a0).comp (listHead ea a0)).congr _ (fun x => by
    simp only [Function.comp_apply,List.head?_drop])
noncomputable def listEraseIdx : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.take x.2++(x.1.drop x.2).tail) :=
  (((listSplitAt ea a0).comp ((listTail ea a0).second (encodeList ea))).comp (listAppend ea a0)).congr _ (fun _ => rfl)
noncomputable def listInsertAt : PolyProgram (encodePair (encodePair (encodeList ea) Nat.bits) ea)
    (encodeList ea) (fun x : (List α × ℕ) × α => x.1.1.take x.1.2++x.2::x.1.1.drop x.1.2) := by
  let sp := (fst (encodePair (encodeList ea) Nat.bits) ea).comp (listSplitAt ea a0)
  let pre := sp.comp (fst (encodeList ea) (encodeList ea))
  let suf := sp.comp (snd (encodeList ea) (encodeList ea))
  let elem := snd (encodePair (encodeList ea) Nat.bits) ea
  exact ((pre.fanout ((elem.fanout suf).comp (listCons ea))).comp (listAppend ea a0)).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListZip -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListZip
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
abbrev enc : (List α × List β) × List (α × β) → List Bool :=
  encodePair (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
def body (x : (List α × List β) × List (α × β)) : List (α × β) ⊕ ((List α × List β) × List (α × β)) :=
  if x.1.1.isEmpty || x.1.2.isEmpty then .inl x.2.reverse
  else .inr ((x.1.1.tail,x.1.2.tail),(x.1.1.head?.getD a0,x.1.2.head?.getD b0)::x.2)
def result (x : (List α × List β) × List (α × β)) : List (α × β) := x.2.reverse++x.1.1.zip x.1.2
noncomputable def program : PolyProgram (enc ea eb) (encodeLoop (enc ea eb) (encodeList (encodePair ea eb))) (body a0 b0) := by
  let pair := PolyProgram.fst (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
  let as := pair.comp (PolyProgram.fst (encodeList ea) (encodeList eb))
  let bs := pair.comp (PolyProgram.snd (encodeList ea) (encodeList eb))
  let cs := PolyProgram.snd (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
  let test := (((as.comp (PolyProgram.listIsEmpty ea)).fanout (bs.comp (PolyProgram.listIsEmpty eb))).comp PolyProgram.boolOr)
  let done := ((cs.comp (PolyProgram.listReverse (encodePair ea eb) (a0,b0))).comp (PolyProgram.injectLeft (enc ea eb) (encodeList (encodePair ea eb))))
  let heads := (as.comp (PolyProgram.listHead ea a0)).fanout (bs.comp (PolyProgram.listHead eb b0))
  let tails := (as.comp (PolyProgram.listTail ea a0)).fanout (bs.comp (PolyProgram.listTail eb b0))
  let push := ((heads.fanout cs).comp (PolyProgram.listCons (encodePair ea eb)))
  let cont := ((tails.fanout push).comp (PolyProgram.injectRight (enc ea eb) (encodeList (encodePair ea eb))))
  exact (PolyProgram.ite test cont done).congr _ (fun _ => rfl)

 theorem run (as : List α) (bs : List β) (cs : List (α × β)) (S : ℕ)
    (hsize : (enc ea eb ((as,bs),cs)).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea eb) (body a0 b0) S t ((as,bs),cs) (result ((as,bs),cs)) := by
  induction as generalizing bs cs with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp [body,result]
  | cons a as ih =>
      cases bs with
      | nil =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp [body,result]
      | cons b bs =>
          have hs : (enc ea eb ((as,bs),(a,b)::cs)).length ≤ S := by
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih bs ((a,b)::cs) hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have he : result ((as,bs),(a,b)::cs)=result ((a::as,b::bs),cs) := by
            simp only [result,List.reverse_cons,List.zip_cons_cons,List.append_assoc,List.singleton_append]
          rw [← he]
          exact BoundedRun.step hsize (by simp [body]) hr

noncomputable def loop : PolyProgram (enc ea eb) (encodeList (encodePair ea eb)) result :=
  (program ea eb a0 b0).loop result (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea eb a0 b0 x.1.1 x.1.2 x.2 (enc ea eb x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListZip
namespace PolyProgram
variable {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
noncomputable def listZip : PolyProgram (encodePair (encodeList ea) (encodeList eb))
    (encodeList (encodePair ea eb)) (fun x : List α × List β => x.1.zip x.2) := by
  let start := (identity (encodePair (encodeList ea) (encodeList eb))).fanout
    (constant (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb)) [])
  exact (start.comp (ListZip.loop ea eb a0 b0)).congr _ (fun _ => by simp only [Function.comp_apply,id_eq,ListZip.result,List.reverse_nil,List.nil_append])
noncomputable def listZipWith {ec : γ → List Bool} {f : α × β → γ}
    (P : PolyProgram (encodePair ea eb) ec f) :
    PolyProgram (encodePair (encodeList ea) (encodeList eb)) (encodeList ec) (fun x : List α × List β => (x.1.zip x.2).map f) :=
  ((listZip ea eb a0 b0).comp (P.listMap (a0,b0))).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryPredicates -/
section
namespace OAI


                                        
section
namespace MetricKMedian.Binary.PolyProgram
noncomputable def natLE : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1≤x.2)) :=
  (((exchange Nat.bits Nat.bits).comp natLT).comp boolNot).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [Function.comp_def,h,not_lt.mpr h]
    · simp [Function.comp_def,h,lt_of_not_ge h])
noncomputable def natEQ : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1=x.2)) :=
  ((natLE.fanout ((exchange Nat.bits Nat.bits).comp natLE)).comp boolAnd).congr _ (fun x => by
    by_cases h₁ : x.1≤x.2 <;> by_cases h₂ : x.2≤x.1 <;> simp [Function.comp_apply,Prod.swap,h₁,h₂,le_antisymm_iff])
noncomputable def ratZero : PolyProgram Ratio.encode encodeBool (fun q => decide (q=0)) :=
  ((ratNum.comp intAbs).comp natZero).congr _ (fun q => by
    simp only [Function.comp_apply,Int.natAbs_eq_zero,Rat.num_eq_zero])
noncomputable def ratNonzero : PolyProgram Ratio.encode encodeBool (fun q => decide (q≠0)) :=
  (ratZero.comp boolNot).congr _ (fun q => by simp)
noncomputable def ratEQ : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1=x.2)) :=
  (ratSub.comp ratZero).congr _ (fun q => by simp only [Function.comp_apply,sub_eq_zero])
noncomputable def ratLE : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1≤x.2)) :=
  (((exchange Ratio.encode Ratio.encode).comp ratLT).comp boolNot).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [Function.comp_def,h,not_lt.mpr h]
    · simp [Function.comp_def,h,lt_of_not_ge h])
end MetricKMedian.Binary.PolyProgram
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListSelection -/
section
namespace OAI


                                           
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListFindIdx
variable {α : Type} (ea : α → List Bool) (a0 : α) (p : α → Bool)
abbrev enc : List α × ℕ → List Bool := encodePair (encodeList ea) Nat.bits
def body (x : List α × ℕ) : ℕ ⊕ (List α × ℕ) :=
  if x.1.isEmpty || p (x.1.head?.getD a0) then .inl x.2 else .inr (x.1.tail,x.2+1)
def result (x : List α × ℕ) : ℕ := x.2+x.1.findIdx p
noncomputable def program (P : PolyProgram ea encodeBool p) :
    PolyProgram (enc ea) (encodeLoop (enc ea) Nat.bits) (body a0 p) := by
  let ls := PolyProgram.fst (encodeList ea) Nat.bits
  let n := PolyProgram.snd (encodeList ea) Nat.bits
  let hd := (ls.comp (PolyProgram.listHead ea a0)).comp P
  let test := ((ls.comp (PolyProgram.listIsEmpty ea)).fanout hd).comp PolyProgram.boolOr
  let done := n.comp (PolyProgram.injectLeft (enc ea) Nat.bits)
  let inc := (n.fanout (PolyProgram.constant (enc ea) Nat.bits 1)).comp PolyProgram.natAdd
  let cont := (((ls.comp (PolyProgram.listTail ea a0)).fanout inc).comp (PolyProgram.injectRight (enc ea) Nat.bits))
  exact (PolyProgram.ite test cont done).congr _ (fun _ => rfl)
 theorem run (as : List α) (n S : ℕ) (hsize : (enc ea (as,n)).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea) (body a0 p) S t (as,n) (result p (as,n)) := by
  induction as generalizing n with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp [body,result]
  | cons a as ih =>
      cases hp : p a with
      | true =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp [body,result,hp,List.findIdx_cons]
      | false =>
          have hn := NatBinary.add_length n 1
          have hs : (enc ea (as,n+1)).length ≤ S := by
            have hone : (1:ℕ).bits.length=1 := rfl
            rw [hone] at hn
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih (n+1) hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have he : result p (as,n+1)=result p (a::as,n) := by simp [result,List.findIdx_cons,hp,Nat.add_comm,Nat.add_left_comm]
          rw [← he]
          exact BoundedRun.step hsize (by simp [body,hp]) hr
noncomputable def loop (P : PolyProgram ea encodeBool p) : PolyProgram (enc ea) Nat.bits (result p) :=
  (program ea a0 p P).loop (result p) (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea a0 p x.1 x.2 (enc ea x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListFindIdx
namespace ListAlgorithms
variable {α : Type}
 theorem foldChoice (p : α × α → Bool) (as : List α) (b : α) :
    as.foldl (fun b a => if p (b,a) then a else b) b=b ∨ as.foldl (fun b a => if p (b,a) then a else b) b∈as := by
  induction as generalizing b with
  | nil => exact Or.inl rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      cases hp : p (b,a)
      · simpa only [hp,Bool.false_eq_true,ite_false] using (ih b).imp_right (fun h => List.mem_cons_of_mem _ h)
      · simp only [ite_true]
        rcases ih a with he|hmem
        · exact Or.inr (by rw [he]; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
end ListAlgorithms
namespace PolyProgram
variable {α : Type} {ea : α → List Bool}
noncomputable def listFindIdx {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) Nat.bits (List.findIdx p) :=
  ((((identity (encodeList ea)).fanout (constant (encodeList ea) Nat.bits 0)).comp
    (ListFindIdx.loop ea a0 p P))).congr _ (fun _ => by simp only [Function.comp_apply,id_eq,ListFindIdx.result,Nat.zero_add])
noncomputable def listChoose {p : α × α → Bool} (P : PolyProgram (encodePair ea ea) encodeBool p) (a0 : α) :
    PolyProgram (encodePair (encodeList ea) ea) ea
      (fun x : List α × α => x.1.foldl (fun b a => if p (b,a) then a else b) x.2) := by
  let step : PolyProgram (encodePair ea ea) ea (fun x => if p x then x.2 else x.1) :=
    (ite P (fst ea ea) (snd ea ea)).congr _ (fun _ => rfl)
  exact step.listFold a0 X (fun as b pre suf he => by
    rcases ListAlgorithms.foldChoice p pre b with h|h
    · rw [h]
      simp only [eval_X,encodePair_length]; omega
    · have hp : (encodeList ea pre).length ≤ (encodeList ea as).length := by
        rw [he,EncodedList.append,List.length_append]; omega
      have hh := (EncodedList.member_length ea pre _ h).trans hp
      simp only [eval_X,encodePair_length]; omega)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Optimization.LPListFacts -/
section
namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset
abbrev Row := List ℚ
abbrev Rows := List Row
abbrev er := Binary.encodeList Binary.Ratio.encode
abbrev ers := Binary.encodeList er

 theorem foldl_max_le {α : Type} [LinearOrder α] (xs : List α) (a b : α)
    (ha : a ≤ b) (hx : ∀ x∈xs, x≤b) : xs.foldl max a ≤ b := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      exact ih (max a x) (max_le ha (hx x List.mem_cons_self)) (fun y hy => hx y (List.mem_cons_of_mem _ hy))

 theorem le_foldl_max {α : Type} [LinearOrder α] (xs : List α) (a : α) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

 theorem member_le_foldl_max {α : Type} [LinearOrder α] (xs : List α) (a b : α) (hb : b∈xs) : b ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => cases hb
  | cons x xs ih =>
      rcases List.mem_cons.mp hb with rfl|hb
      · exact (le_max_right a b).trans (le_foldl_max xs (max a b))
      · exact ih (max a x) hb

 theorem foldl_max_eq {α : Type} [LinearOrder α] (xs : List α) (a b : α)
    (ha : a ≤ b) (hb : b∈xs) (hx : ∀ x∈xs, x≤b) : xs.foldl max a=b :=
  le_antisymm (foldl_max_le xs a b ha hx) (member_le_foldl_max xs a b hb)

 theorem sum_filter_ofFn (n : ℕ) (f : Fin n → ℚ) (p : ℚ → Bool) :
    ((List.ofFn f).filter p).sum=∑ i∈univ.filter (fun i => p (f i)), f i := by
  rw [Finset.sum_filter]
  have he : ((List.ofFn f).filter p).sum=((List.ofFn f).map (fun a => if p a then a else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  rfl

 theorem length_filter_ofFn (n : ℕ) (f : Fin n → ℚ) (p : ℚ → Bool) :
    ((List.ofFn f).filter p).length=(univ.filter (fun i => p (f i))).card := by
  have he : ((List.ofFn f).filter p).length=((List.ofFn f).map (fun a => if p a then (1:ℕ) else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih,Nat.add_comm]
  rw [he,List.map_ofFn,List.sum_ofFn]
  simp

namespace Program
open Binary Binary.PolyProgram
noncomputable def ratMax : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => max x.1 x.2) :=
  (ite ratLE (fst Ratio.encode Ratio.encode) (snd Ratio.encode Ratio.encode)).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [h]
    · simp [h,max_eq_left (le_of_not_ge h)])
noncomputable def ratMin : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => min x.1 x.2) :=
  (ite ratLE (snd Ratio.encode Ratio.encode) (fst Ratio.encode Ratio.encode)).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [h]
    · simp [h,min_eq_right (le_of_not_ge h)])
noncomputable def maxFold : PolyProgram (encodePair er Ratio.encode) Ratio.encode (fun x : Row × ℚ => x.1.foldl max x.2) :=
  (listChoose ratLT 0).congr _ (fun x => by
    congr 1
    funext a b
    by_cases h : a<b
    · simp [h,max_eq_right h.le]
    · simp [h,max_eq_left (le_of_not_gt h)])
end Program
end MetricKMedian.LPBinary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryAutomatic -/
section
namespace OAI


                                       
section
namespace MetricKMedian.Binary.Automatic
open PolyProgram Function
class Coding (α : Type) where
  encode : α → List Bool
abbrev enc {α : Type} [Coding α] : α → List Bool := Coding.encode
instance : Coding ℕ := ⟨Nat.bits⟩
instance : Coding ℤ := ⟨Signed.encode⟩
instance : Coding ℚ := ⟨Ratio.encode⟩
instance : Coding Bool := ⟨encodeBool⟩
instance : Coding Unit := ⟨fun _ => []⟩
instance {α β : Type} [Coding α] [Coding β] : Coding (α × β) := ⟨encodePair enc enc⟩
instance {α : Type} [Coding α] : Coding (List α) := ⟨encodeList enc⟩

@[fun_prop] def Poly {α β : Type} [Coding α] [Coding β] (f : α → β) : Prop :=
  Nonempty (PolyProgram enc enc f)

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
noncomputable def program {f : α → β} (h : Poly f) : PolyProgram enc enc f := Classical.choice h

theorem of_program {f : α → β} (p : PolyProgram enc enc f) : Poly f := ⟨p⟩

@[fun_prop] theorem identity : Poly (id : α → α) := ⟨PolyProgram.identity enc⟩
@[fun_prop] theorem const (b : β) : Poly (fun _ : α => b) := ⟨PolyProgram.constant enc enc b⟩
@[fun_prop] theorem comp {f : β → γ} {g : α → β} (hf : Poly f) (hg : Poly g) : Poly (fun a => f (g a)) :=
  ⟨hg.program.comp hf.program⟩
@[fun_prop] theorem pair {f : α → β} {g : α → γ} (hf : Poly f) (hg : Poly g) : Poly (fun a => (f a,g a)) :=
  ⟨hf.program.fanout hg.program⟩
@[fun_prop] theorem fst : Poly (Prod.fst : α × β → α) := ⟨PolyProgram.fst enc enc⟩
@[fun_prop] theorem snd : Poly (Prod.snd : α × β → β) := ⟨PolyProgram.snd enc enc⟩
@[fun_prop] theorem ite {p : α → Bool} {f g : α → β} (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := ⟨(PolyProgram.ite hp.program hg.program hf.program).congr _ (fun _ => rfl)⟩

@[fun_prop] theorem list_map [Inhabited β] [Inhabited γ] {f : α → β → γ} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).map (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listMapWith default default)⟩

@[fun_prop] theorem rat_add : Poly (fun x : ℚ × ℚ => x.1+x.2) := ⟨ratAdd⟩
@[fun_prop] theorem rat_sub : Poly (fun x : ℚ × ℚ => x.1-x.2) := ⟨ratSub⟩
@[fun_prop] theorem rat_mul : Poly (fun x : ℚ × ℚ => x.1*x.2) := ⟨ratMul⟩
@[fun_prop] theorem rat_div : Poly (fun x : ℚ × ℚ => x.1/x.2) := ⟨ratDiv⟩
@[fun_prop] theorem rat_lt : Poly (fun x : ℚ × ℚ => decide (x.1<x.2)) := ⟨ratLT⟩
@[fun_prop] theorem rat_le : Poly (fun x : ℚ × ℚ => decide (x.1≤x.2)) := ⟨ratLE⟩
@[fun_prop] theorem rat_eq : Poly (fun x : ℚ × ℚ => decide (x.1=x.2)) := ⟨ratEQ⟩
@[fun_prop] theorem rat_min : Poly (fun x : ℚ × ℚ => min x.1 x.2) := ⟨LPBinary.Program.ratMin⟩
@[fun_prop] theorem rat_max : Poly (fun x : ℚ × ℚ => max x.1 x.2) := ⟨LPBinary.Program.ratMax⟩
@[fun_prop] theorem nat_add : Poly (fun x : ℕ × ℕ => x.1+x.2) := ⟨natAdd⟩
@[fun_prop] theorem nat_sub : Poly (fun x : ℕ × ℕ => x.1-x.2) := ⟨natSub⟩
@[fun_prop] theorem nat_mul : Poly (fun x : ℕ × ℕ => x.1*x.2) := ⟨natMul⟩
@[fun_prop] theorem nat_lt : Poly (fun x : ℕ × ℕ => decide (x.1<x.2)) := ⟨natLT⟩
@[fun_prop] theorem nat_le : Poly (fun x : ℕ × ℕ => decide (x.1≤x.2)) := ⟨natLE⟩
@[fun_prop] theorem nat_eq : Poly (fun x : ℕ × ℕ => decide (x.1=x.2)) := ⟨natEQ⟩
@[fun_prop] theorem bool_and : Poly (fun x : Bool × Bool => x.1 && x.2) := ⟨boolAnd⟩
@[fun_prop] theorem bool_or : Poly (fun x : Bool × Bool => x.1 || x.2) := ⟨boolOr⟩
@[fun_prop] theorem rat_neg : Poly (fun x : ℚ => -x) := ⟨ratNeg⟩
@[fun_prop] theorem bool_not : Poly (fun x : Bool => !x) := ⟨boolNot⟩
@[fun_prop] theorem rat_ofNat : Poly (fun x : ℕ => (x:ℚ)) := ⟨ratOfNat⟩
@[fun_prop] theorem rat_ofInt : Poly (fun x : ℤ => (x:ℚ)) := ⟨ratOfInt⟩

@[fun_prop] theorem list_length [Inhabited α] : Poly (List.length : List α → ℕ) := ⟨listLength enc default⟩
@[fun_prop] theorem list_indices [Inhabited α] : Poly (fun xs : List α => List.range xs.length) := ⟨listIndices enc default⟩
@[fun_prop] theorem list_getD (a0 : α) : Poly (fun x : List α × ℕ => x.1[x.2]?.getD a0) := ⟨listGetD enc a0⟩
@[fun_prop] theorem list_head (a0 : α) : Poly (fun xs : List α => xs.head?.getD a0) := ⟨listHead enc a0⟩
@[fun_prop] theorem list_tail [Inhabited α] : Poly (List.tail : List α → List α) := ⟨listTail enc default⟩
@[fun_prop] theorem list_empty : Poly (List.isEmpty : List α → Bool) := ⟨listIsEmpty enc⟩
@[fun_prop] theorem list_append [Inhabited α] : Poly (fun x : List α × List α => x.1++x.2) := ⟨listAppend enc default⟩
@[fun_prop] theorem list_cons : Poly (fun x : α × List α => x.1::x.2) := ⟨listCons enc⟩
@[fun_prop] theorem list_zip [Inhabited α] [Inhabited β] : Poly (fun x : List α × List β => x.1.zip x.2) := ⟨listZip enc enc default default⟩
@[fun_prop] theorem list_filter [Inhabited α] [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).filter (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listFilterWith default default)⟩
@[fun_prop] theorem list_findIdx [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).findIdx (f x)) := by
  let tests := ((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listMapWith default false)
  exact ⟨(tests.comp (listFindIdx (PolyProgram.identity encodeBool) false)).congr _ (fun _ => by
    simp only [Function.comp_def,List.findIdx_map,id_eq])⟩

@[fun_prop] theorem list_getD_comp (a0 : β) {xs : α → List β} {i : α → ℕ}
    (hx : Poly xs) (hi : Poly i) : Poly (fun x => (xs x)[i x]?.getD a0) :=
  comp (list_getD a0) (pair hx hi)
@[fun_prop] theorem list_head_comp (a0 : β) {xs : α → List β}
    (hx : Poly xs) : Poly (fun x => (xs x).head?.getD a0) := comp (list_head a0) hx

@[fun_prop] theorem rat_lt_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x<g x)) := comp rat_lt (pair hf hg)
@[fun_prop] theorem rat_le_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x≤g x)) := comp rat_le (pair hf hg)
@[fun_prop] theorem rat_eq_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x=g x)) := comp rat_eq (pair hf hg)
@[fun_prop] theorem nat_lt_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x<g x)) := comp nat_lt (pair hf hg)
@[fun_prop] theorem nat_le_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x≤g x)) := comp nat_le (pair hf hg)
@[fun_prop] theorem nat_eq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x=g x)) := comp nat_eq (pair hf hg)
@[fun_prop] theorem ite_prop {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : Poly (fun x => decide (p x))) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := by
  exact ⟨(PolyProgram.ite hp.program hg.program hf.program).congr _ (fun _ => by simp only [decide_eq_true_eq])⟩

@[fun_prop] theorem list_flatMap [Inhabited β] [Inhabited γ] {f : α → β → List γ} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).flatMap (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listFlatMapWith default default)⟩

end Poly
end MetricKMedian.Binary.Automatic
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryBooleanLists -/
section
namespace OAI


                                          
section
namespace MetricKMedian.Binary
namespace BooleanLists
def pack : Transducer where
  Q := Unit
  initial := ()
  next := fun _ b => ((),[true,b,false])
  finish := fun _ => []
 theorem pack_run (xs : List Bool) : pack.run () xs=encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [Transducer.run,pack,encodeList,encodeBool,quote,List.append_assoc,List.nil_append] using congrArg (fun ys => [true,b,false]++ys) ih
inductive Phase | start | value | stop deriving DecidableEq
instance : Fintype Phase := ⟨{.start,.value,.stop},by intro p; cases p <;> simp⟩
def unpack : Transducer where
  Q := Phase
  initial := .start
  next := fun q b => match q with
    | .start => (.value,[])
    | .value => (.stop,[b])
    | .stop => (.start,[])
  finish := fun _ => []
 theorem unpack_run (xs : List Bool) : unpack.run .start (encodeList encodeBool xs)=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [encodeList,encodeBool,quote,List.cons_append,List.nil_append,Transducer.run,unpack,List.append_assoc,List.singleton_append] using congrArg (List.cons b) ih
noncomputable def packProgram : PolyProgram id (encodeList encodeBool) (id : List Bool → List Bool) :=
  pack.program.recode id (fun _ => rfl) (fun xs => pack_run xs)
noncomputable def unpackProgram : PolyProgram (encodeList encodeBool) id (id : List Bool → List Bool) :=
  unpack.program.recode (encodeList encodeBool) (fun _ => rfl) (fun xs => unpack_run xs)
noncomputable def valueProgram : PolyProgram (encodeList encodeBool) Nat.bits Word.value := unpackProgram.comp PolyProgram.toBits
 theorem length (xs : List Bool) : (encodeList encodeBool xs).length=3*xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [EncodedList.cons_length,encodeBool,List.length_cons,List.length_nil,ih]; omega
end BooleanLists
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.NumericParserProgram -/
section
namespace OAI


                                            
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
@[fun_prop] theorem take_poly {α : Type} [Coding α] [Inhabited α] : Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨listTake enc default⟩
@[fun_prop] theorem drop_poly {α : Type} [Coding α] [Inhabited α] : Poly (fun x : List α × ℕ => x.1.drop x.2) := ⟨listDrop enc default⟩
@[fun_prop] theorem value_poly : Poly Word.value := ⟨BooleanLists.valueProgram⟩
@[fun_prop] theorem signed_poly : Poly (fun x : Bool × ℕ => Signed.value x.1 x.2) := ⟨intFromParts⟩
@[fun_prop] theorem mkRat_poly : Poly (fun x : ℤ × ℕ => mkRat x.1 x.2) := ⟨mkRational⟩
def width (xs : List Bool) : ℕ := xs.findIdx Bool.not
@[fun_prop] theorem width_poly : Poly width := by unfold width; apply list_findIdx <;> fun_prop
def natRead (xs : List Bool) : ℕ × List Bool :=
  (Word.value ((xs.drop (width xs+1)).take (width xs)),xs.drop (width xs+1+width xs))
@[fun_prop] theorem natRead_poly : Poly natRead := by
  have hd : Poly (fun xs : List Bool => xs.drop (width xs+1)) :=
    Poly.comp (f:=fun x : List Bool × ℕ => x.1.drop x.2) drop_poly (g:=fun xs : List Bool => (xs,width xs+1)) (by fun_prop)
  have ht : Poly (fun xs : List Bool => (xs.drop (width xs+1)).take (width xs)) :=
    Poly.comp (f:=fun x : List Bool × ℕ => x.1.take x.2) take_poly (pair hd width_poly)
  exact pair (Poly.comp value_poly ht) (Poly.comp (f:=fun x : List Bool × ℕ => x.1.drop x.2) drop_poly (g:=fun xs : List Bool => (xs,width xs+1+width xs)) (by fun_prop))
 theorem prefix_width (n : ℕ) (xs : List Bool) : width (List.replicate n true++false::xs)=n := by
  induction n with
  | zero => simp [width,List.findIdx_cons]
  | succ n ih => simp only [List.replicate_succ,List.cons_append,width,List.findIdx_cons,Bool.not_true,Bool.false_eq_true,↓reduceIte]; exact congrArg Nat.succ ih
 theorem natRead_append (n : ℕ) (xs : List Bool) : natRead (encodeNat n++xs)=(n,xs) := by
  unfold natRead
  have hw : width (encodeNat n++xs)=n.bits.length := by
    simpa only [encodeNat,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using prefix_width n.bits.length (n.bits++xs)
  rw [hw]
  have hd : (encodeNat n++xs).drop (n.bits.length+1)=n.bits++xs := by
    simp [encodeNat,List.drop_append,List.append_assoc]
  rw [hd,show (encodeNat n++xs).drop (n.bits.length+1+n.bits.length)=xs from by
    rw [← List.drop_drop,hd,List.drop_left]]
  simp only [List.take_left,Word.value_bits]
 theorem natRead_rest_length (xs : List Bool) : (natRead xs).2.length≤xs.length := by
  simp only [natRead,List.length_drop]; omega
def ratRead (xs : List Bool) : ℚ × List Bool :=
  let a := natRead xs.tail
  let b := natRead a.2
  (mkRat (Signed.value (xs.head?.getD false) a.1) b.1,b.2)
@[fun_prop] theorem ratRead_poly : Poly ratRead := by unfold ratRead; fun_prop
 theorem ratRead_append (q : ℚ) (xs : List Bool) : ratRead (encodeRat q++xs)=(q,xs) := by
  simp only [ratRead,encodeRat,List.append_assoc,List.cons_append,List.tail_cons,List.head?_cons,Option.getD_some,List.nil_append,natRead_append]
  rw [show Signed.value (decide (q.num<0)) q.num.natAbs=q.num from Signed.value_parts q.num]
  rw [Rat.mkRat_eq_div,q.num_div_den]
 theorem ratRead_rest_length (xs : List Bool) : (ratRead xs).2.length≤xs.length :=
  (natRead_rest_length _).trans ((natRead_rest_length _).trans (by simp only [List.length_tail]; omega))
end MetricKMedian.InputParser
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.SequentialParserProgram -/
section
namespace OAI


                                               
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
section Generic
variable {α : Type} [Coding α] [Inhabited α] (read : List Bool → α × List Bool)
abbrev State := List Bool × List α
def parseStep (x : State (α:=α) × Unit) : State (α:=α) :=
  let s := read x.1.1
  (s.2,s.1::x.1.2)
 omit [Inhabited α] in
 theorem parseStep_poly (h : Poly read) : Poly (parseStep read) := by
  unfold parseStep
  have hh : Poly (fun x : State (α:=α) × Unit => read x.1.1) := Poly.comp h (by fun_prop)
  have ha : Poly (fun x : State (α:=α) × Unit => (read x.1.1).1 :: x.1.2) :=
    Poly.comp (f:=fun y : α × List α => y.1::y.2) list_cons (g:=fun x : State (α:=α) × Unit => ((read x.1.1).1,x.1.2)) (by fun_prop)
  exact pair (by fun_prop) ha
variable (P : PolyProgram enc enc read) (hrest : ∀ xs, (read xs).2.length≤xs.length)
noncomputable def parseBound : Polynomial ℕ := X+X*(2*P.sizeBound+1)
 omit [Inhabited α] in
 include hrest in
 theorem parseFold_size (as : List Unit) (b : State (α:=α)) :
    let out := as.foldl (fun b a => parseStep read (b,a)) b
    out.1.length≤b.1.length ∧
    (enc out.2).length≤(enc b.2).length+as.length*(2*P.sizeBound.eval (enc b.1).length+1) := by
  induction as generalizing b with
  | nil => simp only [List.foldl_nil,List.length_nil,zero_mul,add_zero]; exact ⟨le_rfl,le_rfl⟩
  | cons a as ih =>
    have hh := ih (parseStep read (b,a))
    have hr := hrest b.1
    have hs := P.length_bound b.1
    have he : (enc ((read b.1).1)).length ≤ P.sizeBound.eval (enc b.1).length := by
      change (encodePair enc enc (read b.1)).length≤_ at hs
      rw [encodePair_length] at hs
      omega
    have hp : P.sizeBound.eval (enc (read b.1).2).length≤P.sizeBound.eval (enc b.1).length := by
      apply polynomial_eval_mono
      change (encodeList encodeBool (read b.1).2).length≤(encodeList encodeBool b.1).length
      rw [BooleanLists.length,BooleanLists.length]
      omega
    dsimp only [parseStep] at hh
    simp only [List.foldl_cons,List.length_cons]
    refine ⟨hh.1.trans hr,?_⟩
    have hc : (enc ((read b.1).1::b.2)).length=2*(enc (read b.1).1).length+1+(enc b.2).length := EncodedList.cons_length _ _ _
    rw [hc] at hh
    exact hh.2.trans (by nlinarith)
noncomputable def foldProgram : PolyProgram enc enc
    (fun x : List Unit × State (α:=α) => x.1.foldl (fun b a => parseStep read (b,a)) x.2) :=
  (parseStep_poly read ⟨P⟩).program.listFold () (parseBound read P) (by
    intro as b pre suf he
    have hh := parseFold_size read P hrest pre b
    let L := (enc (as,b)).length
    have hb : (enc b).length≤L := by
      dsimp only [L]
      change (enc b).length≤(encodePair enc enc (as,b)).length
      rw [encodePair_length]; dsimp only; omega
    have hp : pre.length≤L := by
      have ha := EncodedList.length_le (enc : Unit → List Bool) as
      have hl : pre.length≤as.length := by rw [he,List.length_append]; omega
      change as.length≤(enc as).length at ha
      dsimp only [L]
      change pre.length≤(encodePair enc enc (as,b)).length
      rw [encodePair_length]; dsimp only; omega
    have hx : (enc b.1).length≤L := by
      change (encodePair enc enc b).length≤L at hb
      rw [encodePair_length] at hb; omega
    have hq := polynomial_eval_mono P.sizeBound hx
    have hr : (enc (pre.foldl (fun b a => parseStep read (b,a)) b).1).length≤(enc b.1).length := by
      change (encodeList encodeBool _).length≤(encodeList encodeBool _).length
      rw [BooleanLists.length,BooleanLists.length]; omega
    change (encodePair enc enc _).length≤_
    rw [encodePair_length]
    change (encodePair enc enc b).length≤L at hb
    rw [encodePair_length] at hb
    simp only [parseBound,eval_add,eval_X,eval_mul,eval_ofNat,eval_one]
    change _≤L+L*(2*P.sizeBound.eval L+1)
    have hm := Nat.mul_le_mul hp (show 2*P.sizeBound.eval (enc b.1).length+1≤2*P.sizeBound.eval L+1 by omega)
    have hh2 := hh.2
    omega)
def parse (x : List Unit × List Bool) : List α × List Bool :=
  let s := x.1.foldl (fun b a => parseStep read (b,a)) (x.2,[])
  (s.2.reverse,s.1)
noncomputable def parseProgram : PolyProgram enc enc (parse read) := by
  have h : Poly (fun x : List Unit × List Bool => (x.1,(x.2,([] : List α)))) := by fun_prop
  have hv : Poly (List.reverse : List α → List α) := ⟨listReverse enc default⟩
  have g : Poly (fun x : State (α:=α) => (x.2.reverse,x.1)) := pair (Poly.comp hv snd) fst
  exact h.program.comp (foldProgram read P hrest) |>.comp g.program
 omit [Coding α] [Inhabited α] in
 theorem parse_fold_encoded (put : α → List Bool) (hr : ∀ a xs, read (put a++xs)=(a,xs))
    (as : List α) (xs : List Bool) (acc : List α) :
    (List.replicate as.length ()).foldl (fun b a => parseStep read (b,a)) ((as.map put).flatten++xs,acc)=
      (xs,as.reverse++acc) := by
  induction as generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp only [List.length_cons,List.replicate_succ,List.map_cons,List.flatten_cons,List.append_assoc,
      List.foldl_cons,parseStep,hr]
    change (List.replicate as.length ()).foldl (fun b a => parseStep read (b,a)) ((as.map put).flatten++xs,a::acc)=_
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
 omit [Coding α] [Inhabited α] in
 theorem parse_encoded (put : α → List Bool) (hr : ∀ a xs, read (put a++xs)=(a,xs))
    (as : List α) (xs : List Bool) :
    parse read (List.replicate as.length (),(as.map put).flatten++xs)=(as,xs) := by
  unfold parse
  rw [parse_fold_encoded read put hr]
  simp
end Generic
end MetricKMedian.InputParser
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryRationalFold -/
section
namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace HasHeight
 theorem foldAdd (as : List ℚ) (b : ℚ) (L : ℕ) (hb : HasHeight b L) :
    HasHeight (as.foldl (·+·) b) (L+(encodeList Ratio.encode as).length) := by
  induction as generalizing b L with
  | nil => simpa only [List.foldl_nil,EncodedList.nil,List.length_nil,add_zero] using hb
  | cons a as ih =>
      have hh := ih (b+a) (L+(Ratio.encode a).length+1) (hb.add (Ratio.height_length a))
      simp only [List.foldl_cons,EncodedList.cons_length]
      exact hh.mono (by omega)
 theorem foldMul (as : List ℚ) (b : ℚ) (L : ℕ) (hb : HasHeight b L) :
    HasHeight (as.foldl (·*·) b) (L+(encodeList Ratio.encode as).length) := by
  induction as generalizing b L with
  | nil => simpa only [List.foldl_nil,EncodedList.nil,List.length_nil,add_zero] using hb
  | cons a as ih =>
      have hh := ih (b*a) (L+(Ratio.encode a).length) (hb.mul (Ratio.height_length a))
      simp only [List.foldl_cons,EncodedList.cons_length]
      exact hh.mono (by omega)
end HasHeight
namespace ListAlgorithms
 theorem foldAdd (as : List ℚ) (b : ℚ) : as.foldl (·+·) b=b+as.sum := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.sum_cons,add_assoc]
 theorem foldMul (as : List ℚ) (b : ℚ) : as.foldl (·*·) b=b*as.prod := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.prod_cons,mul_assoc]
end ListAlgorithms
namespace PolyProgram
noncomputable def ratFoldAdd : PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode)
    Ratio.encode (fun x : List ℚ × ℚ => x.1.foldl (·+·) x.2) :=
  ratAdd.listFold 0 (3*X+10) (fun as b pre suf he => by
    have hh := Ratio.length_height (HasHeight.foldAdd pre b (Ratio.encode b).length (Ratio.height_length b))
    have hp : (encodeList Ratio.encode pre).length ≤ (encodeList Ratio.encode as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [encodePair_length,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
noncomputable def ratFoldMul : PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode)
    Ratio.encode (fun x : List ℚ × ℚ => x.1.foldl (·*·) x.2) :=
  ratMul.listFold 0 (3*X+10) (fun as b pre suf he => by
    have hh := Ratio.length_height (HasHeight.foldMul pre b (Ratio.encode b).length (Ratio.height_length b))
    have hp : (encodeList Ratio.encode pre).length ≤ (encodeList Ratio.encode as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [encodePair_length,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
noncomputable def ratSum : PolyProgram (encodeList Ratio.encode) Ratio.encode List.sum := by
  refine (((identity (encodeList Ratio.encode)).fanout (constant (encodeList Ratio.encode) Ratio.encode 0)).comp ratFoldAdd).congr _ ?_
  intro as
  simp only [Function.comp_apply,id_eq]
  simpa only [zero_add] using ListAlgorithms.foldAdd as 0
noncomputable def ratProd : PolyProgram (encodeList Ratio.encode) Ratio.encode List.prod := by
  refine (((identity (encodeList Ratio.encode)).fanout (constant (encodeList Ratio.encode) Ratio.encode 1)).comp ratFoldMul).congr _ ?_
  intro as
  simp only [Function.comp_apply,id_eq]
  simpa only [one_mul] using ListAlgorithms.foldMul as 1
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end


/- FoldProofs -/
section
namespace DualSepClusterLP.RoundFold

theorem remaining_lt {n : ℕ} {pick : Finset (Fin n) → Finset (Fin n)} (hp : Progress pick)
    (W : Finset (Fin n)) (hne : W.Nonempty) : (W \ pick W).card < W.card := by
  obtain ⟨u,hu⟩ := hp W hne
  obtain ⟨huW,hup⟩ := Finset.mem_inter.mp hu
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
  intro eq
  have : u ∈ W \ pick W := eq.symm ▸ huW
  exact (Finset.mem_sdiff.mp this).2 hup

theorem labelAux_lt {n : ℕ} {pick : Finset (Fin n) → Finset (Fin n)} (hp : Progress pick)
    (f : ℕ) (W : Finset (Fin n)) (hf : W.card ≤ f) (i : Fin n) (hi : i ∈ W) :
    labelAux pick f W i < f := by
  induction f generalizing W with
  | zero => obtain rfl := Finset.card_eq_zero.mp (by omega : W.card=0); simp at hi
  | succ f ih =>
    by_cases h : i ∈ pick W
    · simp [labelAux,h]
    · have hdec := remaining_lt hp W ⟨i,hi⟩
      have hr := ih (W \ pick W) (by omega) (Finset.mem_sdiff.mpr ⟨hi,h⟩)
      simpa [labelAux,h] using hr

def clustering {n : ℕ} (pick : Finset (Fin n) → Finset (Fin n)) (hp : Progress pick) : Clustering n :=
  fun i => ⟨labelAux pick n Finset.univ i,
    labelAux_lt hp n Finset.univ (by simp) i (Finset.mem_univ _)⟩

theorem run_eq_clustering {n : ℕ} (pick : Finset (Fin n) → Finset (Fin n)) (hp : Progress pick) :
    run pick = clustering pick hp := by
  funext i
  have h := labelAux_lt hp n Finset.univ (by simp) i (Finset.mem_univ _)
  simp [run, clustering, h]

private theorem label_zero {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (pick : Finset (Fin n) → Finset (Fin n))
    (f : ℕ) (W : Finset (Fin n)) :
    labelMargin G z B W (labelAux pick (f+1) W) 0 = stepMargin G z B W (pick W) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : i ∈ pick W <;> by_cases hj : j ∈ pick W <;>
    simp [labelEntry, stepEntry, labelAux, hi, hj]

private theorem label_succ {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (pick : Finset (Fin n) → Finset (Fin n))
    (f : ℕ) (W : Finset (Fin n)) (r : ℕ) :
    labelMargin G z B W (labelAux pick (f+1) W) (r+1) =
      labelMargin G z B (W \ pick W) (labelAux pick f (W \ pick W)) r := by
  let K := pick W
  let R := W \ K
  let l := labelAux pick f R
  let l' := labelAux pick (f+1) W
  have point (i j : Fin n) :
      labelEntry G z B l' (r+1) i j =
        if i ∉ K ∧ j ∉ K then labelEntry G z B l r i j else 0 := by
    by_cases hi : i ∈ K <;> by_cases hj : j ∈ K <;>
      simp [l',l,R,K,labelEntry,labelAux,show pick W = K from rfl,hi,hj]
  have eq : R = W.filter (fun i => i ∉ K) := by ext i; simp [R]
  change (∑ i ∈ W, ∑ j ∈ W, labelEntry G z B l' (r+1) i j) = ∑ i ∈ R, ∑ j ∈ R, labelEntry G z B l r i j
  rw [eq]
  simp only [Finset.sum_filter,point]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i ∈ K <;> simp [h]

theorem labelAux_margin {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (pick : Finset (Fin n) → Finset (Fin n))
    (hp : Progress pick) (hg : ∀ W, W.Nonempty → 0 ≤ stepMargin G z B W (pick W))
    (f : ℕ) (W : Finset (Fin n)) (hf : W.card ≤ f) (r : ℕ) :
    0 ≤ labelMargin G z B W (labelAux pick f W) r := by
  induction f generalizing W r with
  | zero => obtain rfl := Finset.card_eq_zero.mp (by omega : W.card=0); simp [labelMargin]
  | succ f ih =>
    rcases W.eq_empty_or_nonempty with rfl | hne
    · simp [labelMargin]
    cases r with
    | zero => simpa only [label_zero] using hg W hne
    | succ r =>
      rw [label_succ]
      have hlt := remaining_lt hp W hne
      exact ih (W \ pick W) (by omega) r

theorem clustering_trace {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (pick : Finset (Fin n) → Finset (Fin n))
    (hp : Progress pick) (hg : ∀ W, W.Nonempty → 0 ≤ stepMargin G z B W (pick W)) :
    RoundTraceOK G (clustering pick hp) z B := by
  intro r
  have h := labelAux_margin G z B pick hp hg n Finset.univ (by simp) r.val
  simpa [roundTraceMargin, labelMargin, labelEntry, clustering, ← Fin.val_eq_val] using h

theorem run_trace {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ) (B : Bool → ℝ → ℝ)
    (pick : Finset (Fin n) → Finset (Fin n)) (hp : Progress pick)
    (hg : ∀ W, W.Nonempty → 0 ≤ stepMargin G z B W (pick W)) :
    RoundTraceOK G (run pick) z B := by
  rw [run_eq_clustering pick hp]
  exact clustering_trace G z B pick hp hg

theorem stepMargin_clock {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (W K : Finset (Fin n)) :
    stepMargin G z clusterEdgeBudget W K =
      ∑ i ∈ W, ∑ j ∈ W, if i < j then clockPairSlack G z K i j else 0 := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i < j <;> by_cases hi : i ∈ K <;> by_cases hj : j ∈ K <;>
    cases hg : G i j <;> simp [stepEntry,clockPairSlack,h,hi,hj,hg]

end DualSepClusterLP.RoundFold
end

/- WordRound -/
section
namespace DualSepClusterLP.WordRound
open OAI.MetricKMedian.Binary

abbrev Word := List Bool
abbrev raw : Word → List Bool := id
abbrev encB := encodeList encodeBool

def zip (f : Bool × Bool → Bool) (a b : Word) : Word := (a.zip b).map f

def square (f : Bool × Bool → Bool) (w : Word) : Word :=
  w.flatMap (fun a => w.map (fun b => f (a,b)))

noncomputable def zipProgram (f : Bool × Bool → Bool) :
    PolyProgram (encodePair raw raw) raw (fun x => zip f x.1 x.2) := by
  open PolyProgram in
  let p := boolFunction (encodePair encodeBool encodeBool) encodeBool f
    (encodePair_injective encodeBool_injective encodeBool_injective)
  let a := (fst raw raw).comp BooleanLists.packProgram
  let b := (snd raw raw).comp BooleanLists.packProgram
  exact (((a.fanout b).comp (listZipWith encodeBool encodeBool false false p)).comp
    BooleanLists.unpackProgram).congr _ (fun _ => rfl)

noncomputable def squareProgram (f : Bool × Bool → Bool) : PolyProgram raw raw (square f) := by
  open PolyProgram in
  let p := boolFunction (encodePair encodeBool encodeBool) encodeBool f
    (encodePair_injective encodeBool_injective encodeBool_injective)
  let row := (exchange encB encodeBool).comp (p.listMapWith false false)
  let grid := row.listFlatMapWith false false
  let a := BooleanLists.packProgram
  exact (((a.fanout a).comp grid).comp BooleanLists.unpackProgram).congr _ (fun _ => rfl)

def equalityWord (labels : List ℕ) : Word :=
  labels.flatMap (fun a => labels.map (fun b => decide (a=b)))

noncomputable def equalityProgram :
    PolyProgram (encodeList Nat.bits) raw equalityWord := by
  open PolyProgram in
  let en := encodeList Nat.bits
  let row := (exchange en Nat.bits).comp (natEQ.listMapWith 0 false)
  let a := identity en
  exact (((a.fanout a).comp (row.listFlatMapWith 0 false)).comp
    BooleanLists.unpackProgram).congr _ (fun _ => rfl)

theorem equalityWord_partition {n : ℕ} (C : Clustering n) :
    equalityWord ((List.finRange n).map (fun i => (C i).val)) = partitionOutput C := by
  simp [equalityWord, partitionOutput, matrixBits, List.flatMap_map, Function.comp_def, Fin.ext_iff]

abbrev State (I : Type) := I × Word × Word
abbrev stateEnc {I : Type} (ei : I → Word) := encodePair ei (encodePair raw raw)

def step {I : Type} (choose : I × Word → Word) (s : State I) : State I :=
  let k := zip (fun p => p.1 && p.2) s.2.1 (choose (s.1,s.2.1))
  (s.1, zip (fun p => p.1 && !p.2) s.2.1 k,
        zip (fun p => p.1 || p.2) s.2.2 (square (fun p => p.1 && p.2) k))

noncomputable def stepProgram {I : Type} {ei : I → Word} {choose : I × Word → Word}
    (select : PolyProgram (encodePair ei raw) raw choose) :
    PolyProgram (stateEnc ei) (stateEnc ei) (step choose) := by
  open PolyProgram in
  let ctx := fst ei (encodePair raw raw)
  let pair := snd ei (encodePair raw raw)
  let live := pair.comp (fst raw raw)
  let eq := pair.comp (snd raw raw)
  let q := (ctx.fanout live).comp select
  let k := (live.fanout q).comp (zipProgram (fun p => p.1 && p.2))
  let rest := (live.fanout k).comp (zipProgram (fun p => p.1 && !p.2))
  let together := k.comp (squareProgram (fun p => p.1 && p.2))
  let next := (eq.fanout together).comp (zipProgram (fun p => p.1 || p.2))
  exact (ctx.fanout (rest.fanout next)).congr _ (fun _ => rfl)

theorem step_length {I : Type} (ei : I → Word) (choose : I × Word → Word) (s : State I) :
    (stateEnc ei (step choose s)).length ≤ (stateEnc ei s).length := by
  simp only [stateEnc, step, zip, raw, id_eq, encodePair_length,
    List.length_map, List.length_zip]
  omega

def run {I : Type} (choose : I × Word → Word) (x : I × Word) : Word :=
  (x.2.foldl (fun s _ => step choose s)
    (x.1,x.2,square (fun _ => false) x.2)).2.2

noncomputable def runProgram {I : Type} {ei : I → Word} {choose : I × Word → Word}
    (select : PolyProgram (encodePair ei raw) raw choose) :
    PolyProgram (encodePair ei raw) raw (run choose) := by
  open PolyProgram in
  let ctx := fst ei raw
  let live := snd ei raw
  let seed := ctx.fanout (live.fanout (live.comp (squareProgram (fun _ => false))))
  let ticks := live.comp BooleanLists.packProgram
  let tick := (fst (stateEnc ei) encodeBool).comp (stepProgram select)
  let loop := tick.listFoldLinear false 0 (by
    intro b _
    simpa only [Function.comp_apply, zero_mul, add_zero] using step_length ei choose b)
  let finish := (snd ei (encodePair raw raw)).comp (snd raw raw)
  exact (((ticks.fanout seed).comp loop).comp finish).congr _ (fun _ => rfl)

end DualSepClusterLP.WordRound
end

/- WordRoundSpec -/
section
namespace DualSepClusterLP.WordRound

def mask {n : ℕ} (W : Finset (Fin n)) : Word :=
  (List.finRange n).map (fun i => decide (i ∈ W))

theorem zip_maps {α : Type} (s : List α) (f : Bool × Bool → Bool) (u v : α → Bool) :
    zip f (s.map u) (s.map v) = s.map (fun i => f (u i,v i)) := by
  induction s <;> simp_all [zip]

private theorem matrix_map {n : ℕ} (A : Fin n → Fin n → Bool) :
    matrixBits A = ((List.finRange n).flatMap (fun i => (List.finRange n).map (i,·))).map
      (fun p => A p.1 p.2) := by
  simp [matrixBits, List.map_flatMap, Function.comp_def]

theorem zip_matrix {n : ℕ} (f : Bool × Bool → Bool) (A B : Fin n → Fin n → Bool) :
    zip f (matrixBits A) (matrixBits B) = matrixBits (fun i j => f (A i j, B i j)) := by
  simp only [matrix_map, zip_maps]

theorem square_mask {n : ℕ} (W : Finset (Fin n)) (f : Bool × Bool → Bool) :
    square f (mask W) = matrixBits (fun i j => f (decide (i∈W),decide (j∈W))) := by
  simp [square, mask, matrixBits, List.flatMap_map, Function.comp_def]

private theorem step_compute {I : Type} {n : ℕ} (ctx : I) (choose : I × Word → Word)
    (pick : Finset (Fin n) → Finset (Fin n))
    (hs : ∀ W, choose (ctx,mask W) = mask (pick W))
    (W : Finset (Fin n)) (A : Fin n → Fin n → Bool) :
    step choose (ctx,mask W,matrixBits A) =
      (ctx, mask (W \ pick W), matrixBits (fun i j => A i j ||
        (decide (i ∈ W ∩ pick W) && decide (j ∈ W ∩ pick W)))) := by
  have hk : zip (fun p => p.1 && p.2) (mask W) (choose (ctx,mask W)) = mask (W ∩ pick W) := by
    rw [hs]
    simp [mask, zip_maps]
  have hw : zip (fun p => p.1 && !p.2) (mask W) (mask (W ∩ pick W)) = mask (W \ pick W) := by
    simp only [mask,zip_maps]
    congr 1
    funext i
    by_cases hi : i ∈ W <;> by_cases hk : i ∈ pick W <;> simp [hi,hk]
  simp only [step, hk, hw, square_mask, zip_matrix]

private theorem fold_compute {I : Type} {n : ℕ} (ctx : I) (choose : I × Word → Word)
    (pick : Finset (Fin n) → Finset (Fin n))
    (hs : ∀ W, choose (ctx,mask W) = mask (pick W)) (hp : RoundFold.Progress pick)
    (ticks : Word) (W : Finset (Fin n)) (A : Fin n → Fin n → Bool)
    (hf : W.card ≤ ticks.length) :
    (ticks.foldl (fun s _ => step choose s) (ctx,mask W,matrixBits A)).2.2 =
      matrixBits (fun i j => A i j || (decide (i∈W) && decide (j∈W) &&
        decide (RoundFold.labelAux pick ticks.length W i = RoundFold.labelAux pick ticks.length W j))) := by
  induction ticks generalizing W A with
  | nil =>
    obtain rfl := Finset.card_eq_zero.mp (by simpa using hf)
    simp
  | cons a xs ih =>
    have hh : (W \ pick W).card ≤ xs.length := by
      by_cases he : W.Nonempty
      · have hh := RoundFold.remaining_lt hp W he
        simp only [List.length_cons] at hf
        omega
      · simpa [Finset.not_nonempty_iff_eq_empty.mp he]
    rw [List.foldl_cons, step_compute ctx choose pick hs, ih _ _ hh]
    congr 1
    funext i j
    by_cases hi : i ∈ W <;> by_cases hj : j ∈ W <;>
      by_cases ki : i ∈ pick W <;> by_cases kj : j ∈ pick W <;>
      simp [List.length_cons, RoundFold.labelAux, hi, hj, ki, kj]

theorem run_partition {I : Type} {n : ℕ} (ctx : I) (choose : I × Word → Word)
    (pick : Finset (Fin n) → Finset (Fin n))
    (hs : ∀ W, choose (ctx,mask W) = mask (pick W)) (hp : RoundFold.Progress pick) :
    run choose (ctx,mask (Finset.univ : Finset (Fin n))) = partitionOutput (RoundFold.run pick) := by
  rw [run, square_mask, fold_compute ctx choose pick hs hp _ _ _ (by simp [mask])]
  rw [RoundFold.run_eq_clustering pick hp]
  simp [mask, partitionOutput, RoundFold.clustering]

end DualSepClusterLP.WordRound
end

/- WordChooser -/
section
namespace DualSepClusterLP.WordRound
open OAI.MetricKMedian.Binary

def upper (w : Word) : Word :=
  let xs := List.range w.length
  xs.flatMap (fun i => xs.map (fun j => decide (i < j)))

noncomputable def upperProgram : PolyProgram raw raw upper := by
  open PolyProgram in
  let en := encodeList Nat.bits
  let row := (exchange en Nat.bits).comp (natLT.listMapWith 0 false)
  let indices := BooleanLists.packProgram.comp (listIndices encodeBool false)
  exact (((indices.fanout indices).comp (row.listFlatMapWith 0 false)).comp
    BooleanLists.unpackProgram).congr _ (fun _ => rfl)

private theorem range_fin (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

theorem upper_mask {n : ℕ} (W : Finset (Fin n)) :
    upper (mask W) = matrixBits (fun i j : Fin n => decide (i < j)) := by
  simp only [upper,mask,List.length_map,List.length_finRange,range_fin,List.flatMap_map,
    List.map_map,Function.comp_def,matrixBits]
  rfl

def cost (upperWord graph eq : Word) : ℕ :=
  (zip (fun p => p.1 && p.2) upperWord (zip (fun p => decide (p.1 ≠ p.2)) graph eq)).countP id

noncomputable def costProgram {I : Type} {ei : I → Word} {u g q : I → Word}
    (up : PolyProgram ei raw u) (graph : PolyProgram ei raw g) (eq : PolyProgram ei raw q) :
    PolyProgram ei Nat.bits (fun x => cost (u x) (g x) (q x)) := by
  open PolyProgram in
  let mismatch := (graph.fanout eq).comp (zipProgram (fun p => decide (p.1 ≠ p.2)))
  let masked := (up.fanout mismatch).comp (zipProgram (fun p => p.1 && p.2))
  let flags := masked.comp BooleanLists.packProgram
  let bad := flags.comp (listFilter (identity encodeBool) false)
  exact (bad.comp (listLength encodeBool false)).congr _ (fun _ => List.countP_eq_length_filter.symm)

private theorem count_map {α : Type} (xs : List α) (p : α → Bool) :
    (xs.map p).countP id = (xs.map (fun a => if p a then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases h : p x <;> simp [h, ih, Nat.add_comm]

theorem count_matrix {n : ℕ} (A : Fin n → Fin n → Bool) :
    (matrixBits A).countP id = ∑ i, ∑ j, if A i j then 1 else 0 := by
  simp only [matrixBits, List.countP_flatMap, Function.comp_def, count_map]
  simp only [← List.ofFn_eq_map, List.sum_ofFn]

theorem cost_eq_disagreements {n : ℕ} (G : Graph n) (C : Clustering n) :
    cost (matrixBits (fun i j : Fin n => decide (i<j)))
      (matrixBits (fun i j => if i < j then G i j else false)) (partitionOutput C) =
      disagreements G C := by
  simp only [cost, partitionOutput, zip_matrix, count_matrix, disagreements]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j <;> simp [h]

def cheaper (u g a b : Word) : Word :=
  if cost u g a ≤ cost u g b then a else b

noncomputable def cheaperProgram {I : Type} {ei : I → Word} {u g a b : I → Word}
    (up : PolyProgram ei raw u) (graph : PolyProgram ei raw g)
    (left : PolyProgram ei raw a) (right : PolyProgram ei raw b) :
    PolyProgram ei raw (fun x => cheaper (u x) (g x) (a x) (b x)) := by
  open PolyProgram in
  let ca := costProgram up graph left
  let cb := costProgram up graph right
  let le := (ca.fanout cb).comp natLE
  exact (ite le right left).congr _ (fun x => by simp [cheaper])

theorem cheaper_partition {n : ℕ} (G : Graph n) (C D : Clustering n) :
    cheaper (matrixBits (fun i j : Fin n => decide (i<j)))
      (matrixBits (fun i j => if i < j then G i j else false))
      (partitionOutput C) (partitionOutput D) =
      partitionOutput (if disagreements G C ≤ disagreements G D then C else D) := by
  rw [cheaper,cost_eq_disagreements,cost_eq_disagreements]
  split <;> rfl

noncomputable def twoRoundsProgram {I : Type} {ei : I → Word} {p q : I × Word → Word}
    {g : I → Word} (graph : PolyProgram ei raw g)
    (left : PolyProgram (encodePair ei raw) raw p) (right : PolyProgram (encodePair ei raw) raw q) :
    PolyProgram (encodePair ei raw) raw (fun x =>
      cheaper (upper x.2) (g x.1) (run p x) (run q x)) :=
  cheaperProgram ((PolyProgram.snd ei raw).comp upperProgram) ((PolyProgram.fst ei raw).comp graph)
    (runProgram left) (runProgram right)

end DualSepClusterLP.WordRound
end

/- TotalWordRound -/
section
namespace DualSepClusterLP.WordRound
open OAI.MetricKMedian.Binary

abbrev PointState (I : Type) := (I × ℕ) × Word × ℕ
abbrev pointEnc {I : Type} (ei : I → Word) :=
  encodePair (encodePair ei Nat.bits) (encodePair raw Nat.bits)

def pointStep {I : Type} (choose : I × Word → Word) (s : PointState I) : PointState I :=
  let k := choose (s.1.1,s.2.1)
  if k[s.1.2]?.getD false then s
  else (s.1,zip (fun p => p.1 && !p.2) s.2.1 k,s.2.2+1)

noncomputable def pointStepProgram {I : Type} {ei : I → Word} {choose : I × Word → Word}
    (select : PolyProgram (encodePair ei raw) raw choose) :
    PolyProgram (pointEnc ei) (pointEnc ei) (pointStep choose) := by
  open PolyProgram in
  let ec := encodePair ei Nat.bits
  let ew := encodePair raw Nat.bits
  let fixed := fst ec ew
  let ctx := fixed.comp (fst ei Nat.bits)
  let i := fixed.comp (snd ei Nat.bits)
  let pair := snd ec ew
  let w := pair.comp (fst raw Nat.bits)
  let c := pair.comp (snd raw Nat.bits)
  let k := (ctx.fanout w).comp select
  let hit := ((k.comp BooleanLists.packProgram).fanout i).comp (listGetD encodeBool false)
  let unpicked := (w.fanout k).comp (zipProgram (fun p => p.1 && !p.2))
  let inc := (c.fanout (constant (pointEnc ei) Nat.bits 1)).comp natAdd
  let next := fixed.fanout (unpicked.fanout inc)
  exact (ite hit next (identity (pointEnc ei))).congr _ (fun _ => rfl)

private theorem point_growth {I : Type} (ei : I → Word) (choose : I × Word → Word) (s : PointState I) :
    (pointEnc ei (pointStep choose s)).length ≤ (pointEnc ei s).length+2 := by
  simp only [pointStep]
  split
  · omega
  · have hh := NatBinary.add_length s.2.2 1
    have hone : (1:ℕ).bits.length=1 := rfl
    rw [hone] at hh
    simp only [pointEnc,encodePair_length,zip,raw,id_eq,List.length_zip,List.length_map]
    omega

def labelCount {I : Type} (choose : I × Word → Word) (x : (I × Word) × ℕ) : ℕ :=
  (x.1.2.foldl (fun s _ => pointStep choose s) ((x.1.1,x.2),x.1.2,0)).2.2

noncomputable def labelCountProgram {I : Type} {ei : I → Word} {choose : I × Word → Word}
    (select : PolyProgram (encodePair ei raw) raw choose) :
    PolyProgram (encodePair (encodePair ei raw) Nat.bits) Nat.bits (labelCount choose) := by
  open PolyProgram in
  let pair := fst (encodePair ei raw) Nat.bits
  let ctx := pair.comp (fst ei raw)
  let w := pair.comp (snd ei raw)
  let i := snd (encodePair ei raw) Nat.bits
  let seed := (ctx.fanout i).fanout (w.fanout (constant (encodePair (encodePair ei raw) Nat.bits) Nat.bits 0))
  let ticks := w.comp BooleanLists.packProgram
  let tick := (fst (pointEnc ei) encodeBool).comp (pointStepProgram select)
  let loop := tick.listFoldLinear false 2 (by
    intro s b
    have h := point_growth ei choose s
    change (pointEnc ei (pointStep choose s)).length ≤ (pointEnc ei s).length+2*(2*1+1)
    omega)
  let count := (snd (encodePair ei Nat.bits) (encodePair raw Nat.bits)).comp (snd raw Nat.bits)
  exact (((ticks.fanout seed).comp loop).comp count).congr _ (fun _ => rfl)

def finalLabel {I : Type} (choose : I × Word → Word) (x : (I × Word) × ℕ) : ℕ :=
  let c := labelCount choose x
  if c < x.1.2.length then c else x.2

noncomputable def finalLabelProgram {I : Type} {ei : I → Word} {choose : I × Word → Word}
    (select : PolyProgram (encodePair ei raw) raw choose) :
    PolyProgram (encodePair (encodePair ei raw) Nat.bits) Nat.bits (finalLabel choose) := by
  open PolyProgram in
  let pair := fst (encodePair ei raw) Nat.bits
  let w := pair.comp (snd ei raw)
  let n := (w.comp BooleanLists.packProgram).comp (listLength encodeBool false)
  let count := labelCountProgram select
  let good := (count.fanout n).comp natLT
  exact (ite good (snd (encodePair ei raw) Nat.bits) count).congr _ (fun _ => by simp [finalLabel])

def totalRun {I : Type} (choose : I × Word → Word) (x : I × Word) : Word :=
  equalityWord ((List.range x.2.length).map (fun i => finalLabel choose (x,i)))

noncomputable def totalRunProgram {I : Type} {ei : I → Word} {choose : I × Word → Word}
    (select : PolyProgram (encodePair ei raw) raw choose) :
    PolyProgram (encodePair ei raw) raw (totalRun choose) := by
  open PolyProgram in
  let x := identity (encodePair ei raw)
  let w := (snd ei raw).comp BooleanLists.packProgram
  let indices := w.comp (listIndices encodeBool false)
  exact (((x.fanout indices).comp ((finalLabelProgram select).listMapWith 0 0)).comp
    equalityProgram).congr _ (fun _ => rfl)

private theorem mask_at {n : ℕ} (W : Finset (Fin n)) (i : Fin n) :
    (mask W)[i.val]?.getD false = decide (i∈W) := by simp [mask,i.isLt]

private theorem mask_sdiff {n : ℕ} (W K : Finset (Fin n)) :
    zip (fun p => p.1 && !p.2) (mask W) (mask K) = mask (W \ K) := by
  simp [mask,zip_maps]

private theorem label_fold {I : Type} {n : ℕ} (ctx : I) (choose : I × Word → Word)
    (pick : Finset (Fin n) → Finset (Fin n))
    (hs : ∀ W, choose (ctx,mask W) = mask (pick W))
    (ticks : Word) (W : Finset (Fin n)) (i : Fin n) (c : ℕ) :
    (ticks.foldl (fun s _ => pointStep choose s) ((ctx,i.val),mask W,c)).2.2 =
      c + RoundFold.labelAux pick ticks.length W i := by
  induction ticks generalizing W c with
  | nil => simp [RoundFold.labelAux]
  | cons b ticks ih =>
    by_cases hi : i ∈ pick W
    · have hs' : pointStep choose ((ctx,i.val),mask W,c) = ((ctx,i.val),mask W,c) := by
        simp [pointStep, hs, mask_at,hi]
      have freeze : ∀ ts : Word, ts.foldl (fun s _ => pointStep choose s) ((ctx,i.val),mask W,c) =
          ((ctx,i.val),mask W,c) := by
        intro ts
        induction ts with
        | nil => rfl
        | cons t ts h => simpa [List.foldl_cons,hs'] using h
      simp [freeze,RoundFold.labelAux,hi]
    · have hs' : pointStep choose ((ctx,i.val),mask W,c) = ((ctx,i.val),mask (W \ pick W),c+1) := by
        simp [pointStep, hs, mask_at, hi, mask_sdiff]
      rw [List.foldl_cons,hs',ih]
      simp only [List.length_cons,RoundFold.labelAux,if_neg hi]
      omega

theorem totalRun_partition {I : Type} {n : ℕ} (ctx : I) (choose : I × Word → Word)
    (pick : Finset (Fin n) → Finset (Fin n)) (hs : ∀ W, choose (ctx,mask W) = mask (pick W)) :
    totalRun choose (ctx,mask (Finset.univ : Finset (Fin n))) = partitionOutput (RoundFold.run pick) := by
  rw [← equalityWord_partition]
  unfold totalRun
  simp only [mask,List.length_map,List.length_finRange]
  have hr : List.range n = (List.finRange n).map Fin.val := by apply List.ext_getElem <;> simp
  rw [hr, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  change finalLabel choose ((ctx,mask (Finset.univ : Finset (Fin n))),i.val) = (RoundFold.run pick i).val
  have hc : labelCount choose ((ctx,mask (Finset.univ : Finset (Fin n))),i.val) =
      RoundFold.labelAux pick n Finset.univ i := by
    rw [labelCount,label_fold ctx choose pick hs]
    simp [mask]
  have hl : (mask (Finset.univ : Finset (Fin n))).length = n := by simp [mask]
  unfold RoundFold.run
  simp only [finalLabel, hc, hl]
  split <;> simp_all

noncomputable def totalTwoRoundsProgram {I : Type} {ei : I → Word} {p q : I × Word → Word}
    {g : I → Word} (graph : PolyProgram ei raw g)
    (left : PolyProgram (encodePair ei raw) raw p) (right : PolyProgram (encodePair ei raw) raw q) :
    PolyProgram (encodePair ei raw) raw (fun x =>
      cheaper (upper x.2) (g x.1) (totalRun p x) (totalRun q x)) :=
  cheaperProgram ((PolyProgram.snd ei raw).comp upperProgram) ((PolyProgram.fst ei raw).comp graph)
    (totalRunProgram left) (totalRunProgram right)

theorem totalTwoRounds_spec {I : Type} {n : ℕ} (ctx : I) (G : Graph n) (p q : I × Word → Word)
    (clock pivot : Finset (Fin n) → Finset (Fin n))
    (hp : ∀ W, p (ctx,mask W) = mask (clock W))
    (hq : ∀ W, q (ctx,mask W) = mask (pivot W)) :
    let x := (ctx,mask (Finset.univ : Finset (Fin n)))
    let C := RoundFold.run clock
    let P := RoundFold.run pivot
    cheaper (upper x.2) (matrixBits G) (totalRun p x) (totalRun q x) =
      partitionOutput (if disagreements G C ≤ disagreements G P then C else P) := by
  dsimp only
  rw [totalRun_partition ctx p clock hp, totalRun_partition ctx q pivot hq,upper_mask]
  have hc (D : Clustering n) :
      cost (matrixBits (fun i j : Fin n => decide (i<j))) (matrixBits G) (partitionOutput D) =
        disagreements G D := by
    simp only [cost,partitionOutput,zip_matrix,count_matrix,disagreements]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i<j <;> simp [h]
  rw [cheaper,hc,hc]
  split <;> rfl

end DualSepClusterLP.WordRound
end

/- PivotMachines -/
section
namespace DualSepClusterLP.PivotMachines

open OAI.MetricKMedian.Binary

noncomputable section
variable {α : Type} {enc : α → List Bool}
abbrev RP (enc : α → List Bool) (f : α → ℚ) := PolyProgram enc Ratio.encode f

def plus {f g : α → ℚ} (p : RP enc f) (q : RP enc g) :
    RP enc (fun a => f a + g a) := (p.fanout q).comp PolyProgram.ratAdd

def minus {f g : α → ℚ} (p : RP enc f) (q : RP enc g) :
    RP enc (fun a => f a - g a) := (p.fanout q).comp PolyProgram.ratSub

def times {f g : α → ℚ} (p : RP enc f) (q : RP enc g) :
    RP enc (fun a => f a * g a) := (p.fanout q).comp PolyProgram.ratMul

def quotient {f g : α → ℚ} (p : RP enc f) (q : RP enc g) :
    RP enc (fun a => f a / g a) := (p.fanout q).comp PolyProgram.ratDiv

def literal (enc : α → List Bool) (q : ℚ) : RP enc (fun _ => q) :=
  PolyProgram.constant enc Ratio.encode q

def low {f g : α → ℚ} (p : RP enc f) (q : RP enc g) :
    RP enc (fun a => min (f a) (g a)) := by
  refine (PolyProgram.ite ((p.fanout q).comp PolyProgram.ratLT) q p).congr _ ?_
  intro a
  change (if decide (f a < g a) then f a else g a) = _
  by_cases h : f a < g a
  · simp [h,min_eq_left h.le]
  · simp [h,min_eq_right (le_of_not_gt h)]

def high {f g : α → ℚ} (p : RP enc f) (q : RP enc g) :
    RP enc (fun a => max (f a) (g a)) := by
  refine (PolyProgram.ite ((p.fanout q).comp PolyProgram.ratLT) p q).congr _ ?_
  intro a
  change (if decide (f a < g a) then g a else f a) = _
  by_cases h : f a < g a
  · simp [h,max_eq_right h.le]
  · simp [h,max_eq_left (le_of_not_gt h)]

def budget {s : α → Bool} {y : α → ℚ} (ps : PolyProgram enc encodeBool s) (py : RP enc y) :
    RP enc (fun a => SparsePivot.budget (s a) (y a)) := by
  let c := literal enc (2773/1227)
  let two := literal enc 2
  let d := minus (literal enc 1) py
  let den := minus two py
  let pos := quotient (times (times two c) (times d d)) den
  let neg := quotient (times (times c py) (minus (literal enc 3) (times two py))) den
  refine (PolyProgram.ite ps neg pos).congr _ ?_
  intro a
  simp only [SparsePivot.budget,pow_two]

def rescue {y : α → ℚ} (py : RP enc y) : RP enc (fun a => SparsePivot.rescue (y a)) :=
  high (literal enc 0) (low (literal enc 1) (times (literal enc (13/6)) (minus py (literal enc (1/2)))))

def chance {s member : α → Bool} {y : α → ℚ} (ps : PolyProgram enc encodeBool s)
    (py : RP enc y) (pm : PolyProgram enc encodeBool member) :
    RP enc (fun a => SparsePivot.chance (s a) (y a) (member a)) := by
  let q := rescue py
  let one := literal enc 1
  let bit := PolyProgram.ite pm (literal enc 0) one
  let pos := plus (plus py (times (minus one py) q)) (times (minus one q) (minus bit py))
  let neg := low (times (literal enc (3/2)) py) (minus (times (literal enc 2) py) (times py py))
  refine (PolyProgram.ite ps neg pos).congr _ ?_
  intro a
  simp only [SparsePivot.chance,pow_two]

def budgetMachine : PolyProgram (encodePair encodeBool Ratio.encode) Ratio.encode
    (fun p : Bool × ℚ => SparsePivot.budget p.1 p.2) :=
  budget (PolyProgram.fst _ _) (PolyProgram.snd _ _)

def chanceMachine : PolyProgram (encodePair encodeBool (encodePair Ratio.encode encodeBool)) Ratio.encode
    (fun p : Bool × ℚ × Bool => SparsePivot.chance p.1 p.2.1 p.2.2) :=
  chance (PolyProgram.fst _ _) ((PolyProgram.snd _ _).comp (PolyProgram.fst _ _))
    ((PolyProgram.snd _ _).comp (PolyProgram.snd _ _))

/-- Given the signed edge data and join marginals, compute one conditional-gain
entry. The flags mark pivot-incidence and a repeated endpoint, respectively. -/
def entry {n : ℕ} {G : α → Graph n} {L : α → SparseWeights n}
    {u v w : α → Fin n} {x : α → Fin n → ℚ}
    (inc : PolyProgram enc encodeBool (fun a => decide (u a = v a ∨ u a = w a)))
    (same : PolyProgram enc encodeBool (fun a => decide (v a = w a)))
    (suv : PolyProgram enc encodeBool (fun a => unorderedSign (G a) (u a) (v a)))
    (svw : PolyProgram enc encodeBool (fun a => unorderedSign (G a) (v a) (w a)))
    (yuv : RP enc (fun a => SparsePivot.mass (L a) (u a) (v a)))
    (yvw : RP enc (fun a => SparsePivot.mass (L a) (v a) (w a)))
    (pv : RP enc (fun a => x a (v a))) (pw : RP enc (fun a => x a (w a))) :
    RP enc (fun a => SparsePivot.entry (G a) (L a) (u a) (v a) (w a) (x a)) := by
  let j := times pv pw
  let both := plus pv pw
  let two := literal enc 2
  let eq := minus (budget suv yuv) (PolyProgram.ite suv pv (minus (literal enc 1) pv))
  let cost := PolyProgram.ite svw j (minus both (times two j))
  let ne := quotient (minus (times (budget svw yvw) (minus both j)) cost) two
  refine (PolyProgram.ite inc (PolyProgram.ite same ne eq) (literal enc 0)).congr _ ?_
  intro a
  simp only [SparsePivot.entry, decide_eq_true_eq]

end
end DualSepClusterLP.PivotMachines
end

/- DenseGain -/
section
namespace DualSepClusterLP.DenseGain

open OAI.MetricKMedian.Binary
open PivotMachines
noncomputable section

/-- A vertex row carries its index, live flag, pivot flag, and join marginal. -/
abbrev Vtx := ℕ × Bool × Bool × ℚ
/-- A cell carries the sign of its edge and its pair mass. -/
abbrev Cell := Bool × ℚ
abbrev Header := Vtx × Cell
abbrev Row := Header × List Cell
/-- The vertex list, and one dense row for every vertex. -/
abbrev Table := List Vtx × List Row

abbrev ev := encodePair Nat.bits (encodePair encodeBool (encodePair encodeBool Ratio.encode))
abbrev ec := encodePair encodeBool Ratio.encode
abbrev eh := encodePair ev ec
abbrev er := encodePair eh (encodeList ec)
abbrev et := encodePair (encodeList ev) (encodeList er)

def contribution (pair : Header × Vtx × Cell) : ℚ :=
  let (h,w,c) := pair
  let (v,b) := h
  let pv := v.2.2.2
  let pw := w.2.2.2
  if v.2.1 && w.2.1 then
    if v.2.2.1 || w.2.2.1 then 0 else
    if v.1=w.1 then SparsePivot.budget b.1 b.2 - (if b.1 then 1-pv else pv)
    else
      let j := pv*pw
      (SparsePivot.budget c.1 c.2 * (pv+pw-j) - (if c.1 then pv+pw-2*j else j))/2
  else 0

def contributionProgram :
    PolyProgram (encodePair eh (encodePair ev ec)) Ratio.encode contribution := by
  open PolyProgram in
  let h := fst eh (encodePair ev ec)
  let wc := snd eh (encodePair ev ec)
  let v := h.comp (fst ev ec)
  let w := wc.comp (fst ev ec)
  let b := h.comp (snd ev ec)
  let c := wc.comp (snd ev ec)
  let vid := v.comp (fst _ _)
  let wid := w.comp (fst _ _)
  let vinfo := v.comp (snd _ _)
  let winfo := w.comp (snd _ _)
  let alive := ((vinfo.comp (fst _ _)).fanout (winfo.comp (fst _ _))).comp boolAnd
  let vp := vinfo.comp (snd _ _)
  let wp := winfo.comp (snd _ _)
  let incident := ((vp.comp (fst _ _)).fanout (wp.comp (fst _ _))).comp boolOr
  let pv := vp.comp (snd _ _)
  let pw := wp.comp (snd _ _)
  let bv := b.comp (fst _ _)
  let cv := c.comp (fst _ _)
  let bcalc := budget bv (b.comp (snd _ _))
  let ccalc := budget cv (c.comp (snd _ _))
  let enc := encodePair eh (encodePair ev ec)
  let two := literal enc 2
  let anchor := minus bcalc (ite bv pv (minus (literal enc 1) pv))
  let j := times pv pw
  let sum := plus pv pw
  let cost := ite cv j (minus sum (times two j))
  let regular := quotient (minus (times ccalc (minus sum j)) cost) two
  let score := ite ((vid.fanout wid).comp natEQ) regular anchor
  let lived := ite incident score (literal enc 0)
  exact (ite alive (literal enc 0) lived).congr _ (fun a => by
    simp only [contribution,Function.comp_apply,decide_eq_true_eq])

def rowScore (vs : List Vtx) (r : Row) : ℚ :=
  ((vs.zip r.2).map (fun p => contribution (r.1,p))).sum

def rowProgram : PolyProgram (encodePair (encodeList ev) er) Ratio.encode (fun t => rowScore t.1 t.2) := by
  open PolyProgram in
  let vs := fst (encodeList ev) er
  let r := snd (encodeList ev) er
  let h := r.comp (fst eh (encodeList ec))
  let es := r.comp (snd eh (encodeList ec))
  let cells := (vs.fanout es).comp (listZip ev ec default default)
  exact (((h.fanout cells).comp (contributionProgram.listMapWith default 0)).comp ratSum).congr _ (fun _ => rfl)

def score (t : Table) : ℚ := (t.2.map (rowScore t.1)).sum

def program : PolyProgram et Ratio.encode score :=
  ((rowProgram.listMapWith default 0).comp PolyProgram.ratSum).congr _ (fun _ => rfl)

def table {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n))
    (u : Fin n) (x : Fin n → ℚ) : Table :=
  let vs : Fin n → Vtx := fun v => (v.val,decide (v∈W),decide (u=v),x v)
  let cell : Fin n → Fin n → Cell := fun a b => (unorderedSign G a b, SparsePivot.mass L a b)
  ((List.finRange n).map vs, (List.finRange n).map
    (fun v => ((vs v,cell u v),(List.finRange n).map (cell v))))

private theorem row_sum {n : ℕ} (W : Finset (Fin n)) (f : Fin n → ℚ) :
    ((List.finRange n).map (fun v => if v∈W then f v else 0)).sum = ∑ v ∈ W, f v := by
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  simp

theorem score_table {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n))
    (u : Fin n) (x : Fin n → ℚ) :
    score (table G L W u x) = SparsePivot.gain G L W u x := by
  classical
  let vs : Fin n → Vtx := fun v => (v.val,decide (v∈W),decide (u=v),x v)
  let cell : Fin n → Fin n → Cell := fun a b => (unorderedSign G a b, SparsePivot.mass L a b)
  have hz (v : Fin n) : (((List.finRange n).map vs).zip ((List.finRange n).map (cell v))) =
      (List.finRange n).map (fun w => (vs w,cell v w)) := by
    generalize (List.finRange n) = ids
    induction ids with
    | nil => rfl
    | cons i ids ih => simp [ih]
  have hpair (v w : Fin n) :
      contribution ((vs v,cell u v),vs w,cell v w) =
      (if v∈W then (if w∈W then SparsePivot.entry G L u v w x else 0) else 0) := by
    simp [contribution,vs,cell,SparsePivot.entry,Fin.ext_iff, Bool.or_eq_true]
    split_ifs <;> simp_all
  unfold score table SparsePivot.gain
  change (((List.finRange n).map (fun v => ((vs v, cell u v),(List.finRange n).map (cell v)))).map
    (rowScore ((List.finRange n).map vs))).sum = _
  simp only [List.map_map,Function.comp_apply]
  trans ((List.finRange n).map (fun v => if v∈W then ∑ w ∈ W, SparsePivot.entry G L u v w x else 0)).sum
  · congr 1
    apply List.map_congr_left
    intro v _
    simp only [Function.comp_apply,rowScore,hz,List.map_map,Function.comp_def,hpair]
    by_cases h : v∈W
    · simp only [if_pos h]
      apply row_sum
    · simp [h]
  · exact row_sum _ _

end
end DualSepClusterLP.DenseGain
end

/- FixMachine -/
section
namespace DualSepClusterLP.FixMachine
open OAI.MetricKMedian.Binary
open DenseGain PivotMachines
noncomputable section

abbrev Geometry := List (Cell × List Cell)
abbrev eg := encodeList (encodePair ec (encodeList ec))
abbrev evec := encodeList ev
abbrev State := Geometry × List Vtx
abbrev estate := encodePair eg evec

def pack (s : State) : Table := (s.2,(s.2.zip s.1).map (fun p => ((p.1,p.2.1),p.2.2)))

def gain (s : State) : ℚ := score (pack s)

def packProgram : PolyProgram estate et pack := by
  open PolyProgram in
  let v := fst ev (encodePair ec (encodeList ec))
  let desc := snd ev (encodePair ec (encodeList ec))
  let h := v.fanout (desc.comp (fst ec (encodeList ec)))
  let row := h.fanout (desc.comp (snd ec (encodeList ec)))
  let p := (exchange eg evec).comp (listZipWith ev (encodePair ec (encodeList ec)) default default row)
  exact ((snd eg evec).fanout p).congr _ (fun _ => rfl)

def gainProgram : PolyProgram estate Ratio.encode gain := packProgram.comp DenseGain.program

def replace (i : ℕ) (bit : ℚ) (v : Vtx) : Vtx :=
  (v.1,v.2.1,v.2.2.1, if i=v.1 then bit else v.2.2.2)

def update (s : State) (i : ℕ) (bit : ℚ) : State :=
  (s.1,s.2.map (replace i bit))

def updateProgram (bit : ℚ) : PolyProgram (encodePair estate Nat.bits) estate
    (fun p : State × ℕ => update p.1 p.2 bit) := by
  open PolyProgram in
  let i := fst Nat.bits ev
  let v := snd Nat.bits ev
  let vi := v.comp (fst _ _)
  let rest := v.comp (snd _ _)
  let active := rest.comp (fst _ _)
  let rest' := rest.comp (snd _ _)
  let piv := rest'.comp (fst _ _)
  let prob := rest'.comp (snd _ _)
  let newProb := ite ((i.fanout vi).comp natEQ) prob (literal (encodePair Nat.bits ev) bit)
  let newV := vi.fanout (active.fanout (piv.fanout newProb))
  let s := fst estate Nat.bits
  let geom := s.comp (fst eg evec)
  let vs := s.comp (snd eg evec)
  let j := snd estate Nat.bits
  let ws := (j.fanout vs).comp (newV.listMapWith default default)
  exact (geom.fanout ws).congr _ (fun p => by simp only [Function.comp_apply, update, decide_eq_true_eq]; rfl)

def coin (s : State) (i : ℕ) : State :=
  let old := (s.2[i]?.getD default).2.2.2
  if old=0 then update s i 0 else if old=1 then update s i 1 else
  if gain (update s i 1) ≤ gain (update s i 0) then update s i 0 else update s i 1

def coinProgram : PolyProgram (encodePair estate Nat.bits) estate (fun p => coin p.1 p.2) := by
  open PolyProgram in
  let s := fst estate Nat.bits
  let i := snd estate Nat.bits
  let vs := s.comp (snd eg evec)
  let v := (vs.fanout i).comp (listGetD ev default)
  let prob := ((v.comp (snd _ _)).comp (snd _ _)).comp (snd _ _)
  let z := updateProgram 0
  let o := updateProgram 1
  let cmp := ((o.comp gainProgram).fanout (z.comp gainProgram)).comp ratLE
  let nontr := ite cmp o z
  let e1 := (prob.fanout (literal (encodePair estate Nat.bits) 1)).comp ratEQ
  exact (ite (prob.comp ratZero) (ite e1 nontr o) z).congr _ (fun p => by simp only
    [Function.comp_apply,coin,decide_eq_true_eq])

def geometry {n : ℕ} (G : Graph n) (L : SparseWeights n) (u : Fin n) : Geometry :=
  let cell (i j : Fin n) : Cell := (unorderedSign G i j,SparsePivot.mass L i j)
  (List.finRange n).map (fun v => (cell u v,(List.finRange n).map (cell v)))

def vector {n : ℕ} (W : Finset (Fin n)) (u : Fin n) (x : Fin n → ℚ) : List Vtx :=
  (List.finRange n).map (fun v => (v.val,decide (v∈W),decide (u=v),x v))

theorem pack_correct {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n))
    (u : Fin n) (x : Fin n → ℚ) :
    pack (geometry G L u, vector W u x) = table G L W u x := by
  unfold pack geometry vector table
  dsimp only
  congr 1
  have h {α β γ : Type} (ls : List α) (f : α → β) (g : α → γ) :
      (ls.map f).zip (ls.map g) = ls.map (fun a => (f a,g a)) := by
    induction ls with
    | nil => rfl
    | cons a ls ih => simp [ih]
  rw [h,List.map_map]
  rfl
theorem update_correct {n : ℕ} (g : Geometry) (W : Finset (Fin n)) (u i : Fin n)
    (x : Fin n → ℚ) (b : ℚ) :
    update (g,vector W u x) i.val b = (g,vector W u (Function.update x i b)) := by
  unfold update vector
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  by_cases h : v=i
  · subst v; simp [replace]
  · have h' : i.val ≠ v.val := fun e => h (Fin.ext e.symm)
    simp [replace,h', Function.update_of_ne h]

theorem coin_correct {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n))
    (u i : Fin n) (x : Fin n → ℚ) :
    coin (geometry G L u,vector W u x) i.val =
      (geometry G L u,vector W u (Function.update x i (if x i=0 then 0 else if x i=1 then 1 else
        if SparsePivot.gain G L W u (Function.update x i 1) ≤ SparsePivot.gain G L W u (Function.update x i 0)
        then 0 else 1))) := by
  unfold coin
  have hold : ((vector W u x)[i.val]?.getD default).2.2.2 = x i := by
    simp [vector, ← List.ofFn_eq_map]
  simp only [hold,update_correct,gain,pack_correct,score_table]
  split_ifs <;> rfl

end
end DualSepClusterLP.FixMachine
end

/- FixLoop -/
section
namespace DualSepClusterLP.FixMachine
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open DenseGain

def run (is : List ℕ) (s : State) : State := is.foldl coin s

theorem vertex_growth (i : ℕ) (v : Vtx) (b : ℚ) (hb : b=0 ∨ b=1) :
    (ev (replace i b v)).length ≤ (ev v).length + 20 := by
  have h0 : (Ratio.encode 0).length ≤ 20 := by decide
  have h1 : (Ratio.encode 1).length ≤ 20 := by decide
  simp only [ev,replace,encodePair_length]
  split_ifs with h
  · rcases hb with rfl | rfl <;> omega
  · omega

theorem vector_growth (i : ℕ) (vs : List Vtx) (b : ℚ) (hb : b=0 ∨ b=1) :
    (evec (vs.map (replace i b))).length ≤ (evec vs).length + 40*vs.length := by
  induction vs with
  | nil => simp [evec,EncodedList.nil]
  | cons v vs ih =>
    have h := vertex_growth i v b hb
    simp only [evec,List.map_cons, EncodedList.cons_length, List.length_cons] at ih ⊢
    omega

private theorem size_coin (s : State) (i : ℕ) :
    (estate (coin s i)).length ≤ (estate s).length + 40*s.2.length ∧ (coin s i).2.length=s.2.length := by
  have h (b : ℚ) (hb : b=0 ∨ b=1) : (estate (update s i b)).length ≤
      (estate s).length + 40*s.2.length ∧ (update s i b).2.length=s.2.length := by
    have hg := vector_growth i s.2 b hb
    simp only [estate,update,encodePair_length,List.length_map]
    constructor
    · omega
    · trivial
  unfold coin
  dsimp only
  split_ifs <;> first | exact h 0 (Or.inl rfl) | exact h 1 (Or.inr rfl)

private theorem size_steps (is : List ℕ) (s : State) :
    (estate (run is s)).length ≤ (estate s).length + 40*s.2.length*is.length := by
  induction is generalizing s with
  | nil => simp [run]
  | cons i is ih =>
    have hr := ih (coin s i)
    obtain ⟨hb,he⟩ := size_coin s i
    rw [he] at hr
    simp only [run,List.foldl_cons,List.length_cons,Nat.mul_succ] at *
    omega

noncomputable def runProgram : PolyProgram (encodePair (encodeList Nat.bits) estate) estate
    (fun p : List ℕ × State => run p.1 p.2) := by
  open Polynomial in
  refine coinProgram.listFold 0 (X+40*X^2) ?_
  intro is s pre suf he
  have h := size_steps pre s
  have hn := EncodedList.length_le ev s.2
  have hp := EncodedList.length_le Nat.bits pre
  let m := (encodePair (encodeList Nat.bits) estate (is,s)).length
  have hs : (estate s).length ≤ m := by simp only [m,encodePair_length]; omega
  have hvec : s.2.length ≤ m := by
    refine hn.trans (le_trans ?_ hs)
    simp only [estate,evec,encodePair_length]; omega
  have hpre : pre.length ≤ m := by
    simp only [m,he,encodePair_length,EncodedList.append,List.length_append]; omega
  have hg := Nat.mul_le_mul (Nat.mul_le_mul_left 40 hvec) hpre
  change (estate (run pre s)).length ≤ _
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow]
  change _ ≤ m+40*m^2
  calc
    _ ≤ (estate s).length+40*s.2.length*pre.length := h
    _ ≤ m + 40*m*m := Nat.add_le_add hs hg
    _ = m+40*m^2 := by ring

theorem run_correct {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n))
    (u : Fin n) (is : List (Fin n)) (x : Fin n → ℚ) :
    run (is.map Fin.val) (geometry G L u,vector W u x) =
      (geometry G L u, vector W u (SparsePivot.fix (SparsePivot.gain G L W u) is x)) := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
    simp only [run,List.map_cons,List.foldl_cons,coin_correct,SparsePivot.fix]
    apply ih

end DualSepClusterLP.FixMachine
end

/- ClusterMachine -/
section
namespace DualSepClusterLP.FixMachine
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open DenseGain

abbrev Matrix := List (List Cell)
abbrev Data := ((Matrix × List Bool) × ℕ) × List Bool

def makeGeometry (m : Matrix) (u : ℕ) : Geometry :=
  (List.range m.length).map (fun i => (((m[u]?.getD [])[i]?.getD default), m[i]?.getD []))

def makeVertex (a : Data) (i : ℕ) : Vtx :=
  let m := a.1.1.1
  let W := a.1.1.2
  let u := a.1.2
  let S := a.2
  let cell := (m[u]?.getD [])[i]?.getD default
  (i,W[i]?.getD false, decide (u=i),
    if u=i then 1 else SparsePivot.chance cell.1 cell.2 (S[i]?.getD false))

def seed (a : Data) : State :=
  (makeGeometry a.1.1.1 a.1.2, (List.range a.1.1.1.length).map (makeVertex a))

def cluster (a : Data) : List Bool :=
  ((run (List.range a.1.1.1.length) (seed a)).2).map (fun v => v.2.1 && decide (v.2.2.2=1))

@[fun_prop] theorem poly_chance {α : Type} [Coding α] {s m : α → Bool} {y : α → ℚ}
    (hs : Poly s) (hy : Poly y) (hm : Poly m) :
    Poly (fun a => SparsePivot.chance (s a) (y a) (m a)) :=
  ⟨PivotMachines.chance hs.program hy.program hm.program⟩

@[fun_prop] theorem poly_indices_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → List β} (hf : Poly f) : Poly (fun a => List.range (f a).length) :=
  comp (f:=fun xs : List β => List.range xs.length) (g:=f) list_indices hf

@[fun_prop] theorem poly_geometry : Poly (fun p : Matrix × ℕ => makeGeometry p.1 p.2) := by
  unfold makeGeometry
  apply list_map
  · fun_prop
  · apply poly_indices_comp; exact fst

@[fun_prop] theorem poly_vertex : Poly (fun p : Data × ℕ => makeVertex p.1 p.2) := by
  unfold makeVertex
  fun_prop

@[fun_prop] theorem poly_seed : Poly seed := by
  unfold seed
  apply pair
  · exact comp (g:=fun p : Data => (p.1.1.1,p.1.2)) poly_geometry (by fun_prop)
  · apply list_map
    · exact poly_vertex
    · fun_prop

@[fun_prop] theorem poly_run : Poly (fun p : List ℕ × State => run p.1 p.2) := ⟨runProgram⟩

@[fun_prop] theorem poly_cluster : Poly cluster := by
  unfold cluster
  apply list_map
  · fun_prop
  · apply comp (f:=Prod.snd) snd
    exact comp (g:=fun p : Data => (List.range p.1.1.1.length,seed p)) poly_run (by fun_prop)

def matrixOf {n : ℕ} (G : Graph n) (L : SparseWeights n) : Matrix :=
  (List.finRange n).map (fun i => (List.finRange n).map (fun j => (unorderedSign G i j,SparsePivot.mass L i j)))

def mask {n : ℕ} (S : Finset (Fin n)) : List Bool := (List.finRange n).map (fun i => decide (i∈S))

private theorem range_val (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

private theorem fin_get {n : ℕ} {α : Type} (f : Fin n → α) (i : Fin n) (d : α) :
    (((List.finRange n).map f)[i.val]?.getD d) = f i := by
  simp [←List.ofFn_eq_map]

theorem geom_correct {n : ℕ} (G : Graph n) (L : SparseWeights n) (u : Fin n) :
    makeGeometry (matrixOf G L) u.val = geometry G L u := by
  simp only [makeGeometry,geometry,matrixOf,List.length_map,List.length_finRange,range_val,List.map_map,
    Function.comp_def,fin_get]

theorem vertex_correct {n : ℕ} (G : Graph n) (L : SparseWeights n) (W S : Finset (Fin n)) (u i : Fin n) :
    makeVertex (((matrixOf G L,mask W),u.val),mask S) i.val =
      (i.val,decide (i∈W),decide (u=i),SparsePivot.initial G L u S i) := by
  simp only [makeVertex,matrixOf,mask,fin_get,SparsePivot.initial,Fin.ext_iff,eq_comm]

theorem seed_correct {n : ℕ} (G : Graph n) (L : SparseWeights n) (W S : Finset (Fin n)) (u : Fin n) :
    seed (((matrixOf G L,mask W),u.val),mask S) =
      (geometry G L u,vector W u (SparsePivot.initial G L u S)) := by
  have h : (matrixOf G L).length=n := by simp [matrixOf]
  simp only [seed,geom_correct,h,range_val,List.map_map,Function.comp_def,vertex_correct,vector]

theorem cluster_correct {n : ℕ} (G : Graph n) (L : SparseWeights n) (W S : Finset (Fin n)) (u : Fin n) :
    cluster (((matrixOf G L,mask W),u.val),mask S) = mask (SparsePivot.cluster G L W u S) := by
  have h : (matrixOf G L).length=n := by simp [matrixOf]
  unfold cluster
  rw [h,range_val,seed_correct,run_correct]
  simp only [vector,List.map_map,mask,SparsePivot.cluster]
  apply List.map_congr_left
  intro v _
  simp [Function.comp_def]

end DualSepClusterLP.FixMachine
end

/- PivotSelect -/
section
namespace DualSepClusterLP.PivotSelect
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open WordRound (mask Word)
abbrev Cell := Bool × ℚ
abbrev Matrix := List (List Cell)
abbrev Arg := (((Matrix × Word) × ℕ) × Word)
abbrev Data := (Matrix × List Word) × Word

def matrixOf {n : ℕ} (G : Graph n) (L : SparseWeights n) : Matrix :=
  (List.finRange n).map (fun i => (List.finRange n).map (fun j =>
    (unorderedSign G i j, SparsePivot.mass L i j)))

def ids (x : Word) : List ℕ := List.range x.length
@[fun_prop] theorem ids_poly : Poly ids := Poly.list_indices

@[fun_prop] private theorem sum_poly : Poly (List.sum : List ℚ → ℚ) :=
  ⟨PolyProgram.ratSum⟩

@[fun_prop] private theorem budget_poly : Poly (fun a : Cell => SparsePivot.budget a.1 a.2) :=
  ⟨PivotMachines.budget (PolyProgram.fst _ _) (PolyProgram.snd _ _)⟩

def term (x : ((Matrix × Word) × Word) × (ℕ × ℕ)) : ℚ :=
  let ((m,w),k) := x.1
  let (i,j) := x.2
  let c := (m[i]?.getD [])[j]?.getD (false,0)
  let a := k[i]?.getD false
  let b := k[j]?.getD false
  if decide (i<j) && w[i]?.getD false && w[j]?.getD false then
    (if a || b then SparsePivot.budget c.1 c.2 else 0) -
    (if (if c.1 then ((a && !b) || (!a && b)) else a && b) then 1 else 0)
  else 0

@[fun_prop] theorem term_poly : Poly term := by
  unfold term
  dsimp only
  fun_prop (disch := first | apply Poly.comp budget_poly; fun_prop | assumption)

def margin (x : (Matrix × Word) × Word) : ℚ :=
  ((ids x.1.2).map (fun i => ((ids x.1.2).map (fun j => term (x,(i,j)))).sum)).sum

@[fun_prop] theorem margin_poly : Poly margin := by unfold margin; fun_prop

def candidates (cluster : Arg → Word) (x : Data) : List Word :=
  let ((m,cols),w) := x
  (ids w).flatMap fun u =>
    if w[u]?.getD false then
      (cols.filter (fun s => s[u]?.getD false)).map (fun s => cluster (((m,w),u),s))
    else []

theorem candidates_poly {cluster : Arg → Word} (hc : Poly cluster) : Poly (candidates cluster) := by
  unfold candidates
  dsimp only
  fun_prop

def accepts (x : (Matrix × Word) × Word) : Bool :=
  x.2.any id && decide (0 ≤ margin x)

@[fun_prop] theorem accepts_poly : Poly accepts := by
  have hh : Poly (fun b : Word => b.any id) := ⟨(PolyProgram.identity encodeBool).listAny false⟩
  unfold accepts
  fun_prop

def select (cluster : Arg → Word) (x : Data) : Word :=
  let ks := (candidates cluster x).filter (fun k => accepts ((x.1.1,x.2),k))
  if ks.isEmpty then x.2.map (fun _ => false) else ks.head?.getD []

theorem select_poly {cluster : Arg → Word} (hc : Poly cluster) : Poly (select cluster) := by
  have hh := candidates_poly hc
  unfold select
  fun_prop

private theorem mask_bit {n : ℕ} (W : Finset (Fin n)) (i : Fin n) :
    (mask W)[i.val]?.getD false = decide (i∈W) := by simp [mask,i.isLt]

private theorem ids_mask {n : ℕ} (W : Finset (Fin n)) :
    ids (mask W) = (List.finRange n).map Fin.val := by
  simp only [ids,mask,List.length_map,List.length_finRange]
  apply List.ext_getElem <;> simp

private theorem term_eq {n : ℕ} (G : Graph n) (L : SparseWeights n) (W K : Finset (Fin n)) (v w : Fin n) :
    term (((matrixOf G L,mask W),mask K),(v.val,w.val)) =
      (if v∈W then if w∈W then if v<w then
        (if v∈K ∨ w∈K then SparsePivot.budget (unorderedSign G v w) (SparsePivot.mass L v w) else 0) -
        (if unorderedSign G v w then (if decide (v∈K) != decide (w∈K) then 1 else 0)
        else (if v∈K ∧ w∈K then 1 else 0)) else 0 else 0 else 0) := by
  have cc : ((matrixOf G L)[v.val]?.getD [])[w.val]?.getD (false,0) =
      (unorderedSign G v w,SparsePivot.mass L v w) := by
    simp [matrixOf,← List.ofFn_eq_map,v.isLt,w.isLt]
  simp only [term,mask_bit,cc,← Fin.lt_def]
  by_cases hv : v∈W <;> by_cases hw : w∈W <;> by_cases hvw : v<w <;>
    by_cases kv : v∈K <;> by_cases kw : w∈K <;> cases hh : unorderedSign G v w <;>
    simp [hv,hw,hvw,kv,kw]

theorem margin_exact {n : ℕ} (G : Graph n) (L : SparseWeights n) (W K : Finset (Fin n)) :
    margin ((matrixOf G L,mask W),mask K) = SparsePivot.margin G L W K := by
  simp only [margin,ids_mask,List.map_map,Function.comp_def,term_eq]
  simp only [←List.ofFn_eq_map,List.sum_ofFn,SparsePivot.margin]
  simp [Finset.sum_ite_irrel]

private theorem accepts_exact {n : ℕ} (G : Graph n) (L : SparseWeights n) (W K : Finset (Fin n)) :
    accepts ((matrixOf G L,mask W),mask K) = decide (K.Nonempty ∧ 0 ≤ SparsePivot.margin G L W K) := by
  have hh : (mask K).any id = decide K.Nonempty := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    simp [mask,List.any_eq_true,Finset.Nonempty]
  simp [accepts,hh,margin_exact]

def environment {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n)) : Data :=
  ((matrixOf G L,L.map (fun e => mask e.1)),mask W)

theorem candidates_exact {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n))
    (cluster : Arg → Word)
    (h : ∀ u : Fin n, ∀ S : Finset (Fin n),
      cluster (((matrixOf G L,mask W),u.val),mask S) = mask (SparsePivot.cluster G L W u S)) :
    candidates cluster (environment G L W) = (SparsePivot.candidates G L W).map mask := by
  simp only [candidates,environment,ids_mask,List.flatMap_map,
    SparsePivot.candidates,List.map_flatMap,mask_bit]
  congr 1
  funext u
  by_cases hu : u∈W
  · simp only [hu,decide_true,↓reduceIte]
    have aux (cols : SparseWeights n) :
        (((cols.map (fun e => mask e.1)).filter (fun s => s[u.val]?.getD false)).map
          (fun s => cluster (((matrixOf G L,mask W),u.val),s))) =
        (cols.filterMap (fun e => if u∈e.1 then some (SparsePivot.cluster G L W u e.1) else none)).map mask := by
      induction cols with
      | nil => rfl
      | cons a xs ih =>
        by_cases ha : u∈a.1 <;> simp [mask_bit,ha,h,ih]
    exact aux L
  · simp [hu]

theorem select_exact {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n))
    (cluster : Arg → Word) (hc : ∀ u : Fin n, ∀ S : Finset (Fin n),
      cluster (((matrixOf G L,mask W),u.val),mask S) = mask (SparsePivot.cluster G L W u S)) :
    select cluster (environment G L W) = mask (SparsePivot.step G L W) := by
  rw [select,candidates_exact G L W cluster hc]
  dsimp only [environment]
  have hz : (mask W).map (fun _ => false) = mask (∅ : Finset (Fin n)) := by
    simp [mask,Function.comp_def]
  unfold SparsePivot.step
  generalize SparsePivot.candidates G L W = xs
  induction xs with
  | nil => exact hz
  | cons K xs ih =>
    cases he : decide (K.Nonempty ∧ 0 ≤ SparsePivot.margin G L W K) <;>
      simp only [List.map_cons,List.filter_cons,List.find?_cons,accepts_exact,he,
        Bool.false_eq_true,not_false_eq_true,↓reduceIte, List.isEmpty_cons, List.head?_cons, Option.getD_some] <;>
      first | exact ih | rfl

end DualSepClusterLP.PivotSelect
end

/- WireTM -/
section
namespace DualSepClusterLP.WireTM
open OAI.MetricKMedian OAI.MetricKMedian.InputParser
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly

abbrev Row := List Bool × ℚ
abbrev Out := (ℕ × List Bool) × List Row

@[fun_prop] theorem take_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → ℕ} {g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => (g x).take (f x)) :=
  comp take_poly (pair hg hf)

@[fun_prop] theorem drop_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → ℕ} {g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => (g x).drop (f x)) :=
  comp drop_poly (pair hg hf)

@[fun_prop] theorem append_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x ++ g x) :=
  comp list_append (pair hf hg)

/-- Keep the unary width prefix in the residual word so a single uniform parser
can process any number of sparse columns with the same width. -/
def read (xs : List Bool) : Row × List Bool :=
  let w := width xs
  let mark :=  xs.take (w+1)
  let cols := xs.drop (w+1)
  let p := ratRead (cols.drop w)
  ((cols.take w, p.1),mark ++ p.2)

@[fun_prop] theorem read_poly : Poly read := by unfold read; fun_prop

theorem read_length (xs : List Bool) : (read xs).2.length ≤ xs.length := by
  unfold read
  simp only [List.length_append, List.length_take]
  have h := ratRead_rest_length (((xs.drop (width xs+1)).drop (width xs)))
  simp only [List.length_drop] at h
  omega

def tag (w : ℕ) := List.replicate w true ++ [false]
def put (r : Row) := r.1 ++ priceBits r.2

theorem read_encoded (n : ℕ) (r : Row) (hw : r.1.length=n) (xs : List Bool) :
    read (tag n ++ (put r ++ xs)) = (r,tag n ++ xs) := by
  have ht : (tag n).length=n+1 := by simp [tag]
  have hwid : width (tag n ++ (put r ++ xs)) = n := by simpa [tag,List.append_assoc] using prefix_width n (put r ++ xs)
  simp only [read,hwid]
  rw [←ht,List.take_left,List.drop_left]
  simp only [put,List.append_assoc,←hw,List.take_left,List.drop_left]
  have hp : ratRead (priceBits r.2 ++ xs) = (r.2,xs) := by
    simpa only [priceBits,encodeRat,lengthPrefixedNat,encodeNat,List.cons_append,List.nil_append] using ratRead_append r.2 xs
  rw [hp]

def units (xs : List Bool) (k : ℕ) := (xs.take k).map (fun _ => ())
def parseRows (x : List (Unit) × List Bool) : List Row := (parse read x).1
@[fun_prop] theorem parseRows_poly : Poly parseRows := by
  have h : Poly (parse read) := ⟨parseProgram read read_poly.program read_length⟩
  exact Poly.comp (f:=Prod.fst) (g:=parse read) fst h

def raw (xs : List Bool) : Out :=
  let tail := xs.drop (width xs+1)
  let n := width tail
  let mark :=  tail.take (n+1)
  let body := tail.drop (n+1)
  let m := n*n
  let rows := natRead (body.drop m)
  ((n, body.take m), parseRows (units rows.2 rows.1,mark ++ rows.2))

@[fun_prop] theorem units_comp {α : Type} [Coding α] {xs : α → List Bool} {k : α → ℕ}
    (hx : Poly xs) (hk : Poly k) : Poly (fun x => units (xs x) (k x)) := by
  unfold units
  apply list_map <;> fun_prop

@[fun_prop] theorem raw_poly : Poly raw := by unfold raw; fun_prop

/-- On raw, unquoted input bits this is a stock polynomial-time Turing-machine parser. -/
noncomputable def machine : PolyProgram id enc raw :=
  BooleanLists.packProgram.comp raw_poly.program

def rowOf {n : ℕ} (e : Finset (Fin n) × ℚ) : Row :=
  ((List.finRange n).map (fun i => decide (i∈e.1)), e.2)

theorem parse_on_rows (n : ℕ) (rows : List Row) (hw : ∀ r∈rows, r.1.length = n)
    (xs : List Bool) (acc : List Row) :
    (List.replicate rows.length ()).foldl (fun b a => parseStep read (b,a))
      (tag n ++ (rows.flatMap put ++ xs),acc) = (tag n ++ xs,rows.reverse ++ acc) := by
  induction rows generalizing acc with
  | nil => simp
  | cons r rs ih =>
    simp only [List.length_cons,List.replicate_succ,List.foldl_cons,List.flatMap_cons,List.append_assoc]
    change (List.replicate rs.length ()).foldl (fun b a => parseStep read (b,a)) ( (read (tag n ++ (put r ++ (rs.flatMap put ++ xs)))).2, (read (tag n ++ (put r ++ (rs.flatMap put ++ xs)))).1 :: acc) = _
    rw [read_encoded n r (hw r List.mem_cons_self)]
    rw [ih (fun r hr => hw r (List.mem_cons_of_mem _ hr))]
    simp

private theorem units_full (l : List Bool) (k : ℕ) (h : k ≤ l.length) :
    units l k = List.replicate k () := by
  apply List.eq_replicate_iff.mpr
  exact ⟨by simp [units, Nat.min_eq_left h],fun _ _ => rfl⟩

theorem raw_encoded {n : ℕ} (G : Graph n) (L : SparseWeights n) :
    raw (roundingInput G L) = ((n,matrixBits (fun i j : Fin n => if i<j then G i j else false)), L.map rowOf) := by
  let H := matrixBits (fun i j : Fin n => if i<j then G i j else false)
  let R := L.map rowOf
  let E := R.flatMap put
  have he : roundingInput G L = false :: (tag n ++ (H ++ (lengthPrefixedNat L.length ++ E))) := by
    simp only [roundingInput,graphInput,H,tag,E,R,rowOf,put,List.flatMap_map,List.append_assoc,
      List.replicate_zero,List.nil_append,List.cons_append]
  have hh : H.length = n*n := by
    simp [H,matrixBits,List.length_flatMap,List.map_const',List.sum_replicate]
  have htag : (tag n).length = n+1 := by simp [tag]
  have hwidth : width (tag n ++ (H ++ (lengthPrefixedNat L.length ++ E))) = n := by
    simpa [tag,List.append_assoc] using prefix_width n (H ++ (lengthPrefixedNat L.length ++ E))
  have natok : natRead (lengthPrefixedNat L.length ++ E) = (L.length,E) := natRead_append _ _
  have heL : R.length ≤ E.length := by
    dsimp only [E]
    induction R with
    | nil => simp
    | cons r rs ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append,put,priceBits,List.length_cons] at *
      omega
  have hRL : R.length = L.length := by simp [R]
  have hr : ∀ r∈R, r.1.length=n := by
    intro r h
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp h
    simp [rowOf]
  rw [he]
  change raw (false :: (tag n ++ (H ++ (lengthPrefixedNat L.length ++ E)))) = ((n,H),R)
  have first (ys : List Bool) : width (false :: ys) = 0 := by simp [width,List.findIdx_cons]
  simp only [raw,first,Nat.zero_add,List.drop_succ_cons,List.drop_zero,hwidth,←htag,List.take_left,List.drop_left,←hh,List.take_left,List.drop_left,natok]
  rw [units_full E L.length (hRL ▸ heL), ←hRL]
  unfold parseRows parse
  change ((n,H),_)=_
  have hh' := parse_on_rows n R hr [] []
  simp only [List.append_nil] at hh'
  rw [hh']
  simp

noncomputable def machine_encoded {n : ℕ} (G : Graph n) (L : SparseWeights n) :
    Turing.TM2OutputsInTime machine.machine.tm (roundingInput G L)
      (some (enc ((n,matrixBits (fun i j : Fin n => if i<j then G i j else false)),L.map rowOf)))
      (machine.time.eval (roundingInput G L).length) := by
  simpa only [raw_encoded,id_eq] using machine.outputs (roundingInput G L)

end DualSepClusterLP.WireTM
end

/- WireAll -/
section
namespace DualSepClusterLP.WireTM
open OAI.MetricKMedian.InputParser OAI.MetricKMedian.Binary

theorem unary_all (xs : List Bool) :
    RoundWire.unary xs = (width xs,xs.drop (width xs+1)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp [RoundWire.unary,ih,width,List.findIdx_cons,List.drop_succ_cons]

private theorem bits_all (xs : List Bool) : Word.value xs = xs.foldr Nat.bit 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Nat.bit_val,ih]; omega

theorem nat_all (xs : List Bool) : natRead xs = RoundWire.natField xs := by
  simp [natRead,RoundWire.natField,unary_all,bits_all,List.drop_drop]

theorem price_all (xs : List Bool) : ratRead xs = RoundWire.priceField xs := by
  simp [ratRead,RoundWire.priceField,nat_all,Signed.value,List.headD_eq_head?_getD]

def cols (n : ℕ) : ℕ → List Bool → List Row × List Bool
  | 0,xs => ([],xs)
  | k+1,xs =>
    let p := RoundWire.priceField (xs.drop n)
    let t := cols n k p.2
    ((xs.take n,p.1)::t.1,t.2)

private theorem read_tag (n : ℕ) (xs : List Bool) :
    read (tag n ++ xs) =
      ((xs.take n,(RoundWire.priceField (xs.drop n)).1),
        tag n ++ (RoundWire.priceField (xs.drop n)).2) := by
  have h : width (tag n ++ xs) = n := by simpa [tag,List.append_assoc] using prefix_width n xs
  have ht : (tag n).length = n+1 := by simp [tag]
  simp only [read,h,←ht,List.drop_left,List.take_left,price_all]

private theorem fold_all (n k : ℕ) (xs : List Bool) (acc : List Row) :
    (List.replicate k ()).foldl (fun b a => parseStep read (b,a)) (tag n ++ xs,acc) =
      (tag n ++ (cols n k xs).2,(cols n k xs).1.reverse ++ acc) := by
  induction k generalizing xs acc with
  | zero => simp [cols]
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons]
    change (List.replicate k ()).foldl _ ((read (tag n ++ xs)).2,(read (tag n ++ xs)).1::acc) = _
    rw [read_tag,ih]
    simp [cols]

private theorem parse_all (n k : ℕ) (xs : List Bool) :
    parseRows (units xs k,tag n ++ xs) = (cols n (min k xs.length) xs).1 := by
  have h : units xs k = List.replicate (min k xs.length) () := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp [units],fun _ _ => rfl⟩
  simp [parseRows,parse,h,fold_all]

private def asColumn (n : ℕ) (r : Row) : Finset (Fin n) × ℚ :=
  (Finset.univ.filter (fun i : Fin n => r.1.getD i.val false),r.2)

private theorem cols_entries (n k : ℕ) (xs : List Bool) :
    (cols n k xs).1.map (asColumn n) = RoundWire.readEntries n k xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    simp only [cols,RoundWire.readEntries,List.map_cons,ih,asColumn]
    congr 2
    ext i
    simp [List.getD_eq_getElem?_getD,List.getElem?_take,i.isLt]

def view (x : Out) : (n : ℕ) × (Graph n × SparseWeights n) :=
  ⟨x.1.1,fun i j => (x.1.2)[i.val*x.1.1+j.val]?.getD false,x.2.map (asColumn x.1.1)⟩

private theorem remaining (n k : ℕ) (xs : List Bool) :
    (RoundWire.readRows n k xs).2 = xs.drop (k*n) := by
  induction k generalizing xs with
  | zero => simp [RoundWire.readRows]
  | succ k ih => simp [RoundWire.readRows,ih,List.drop_drop,Nat.succ_mul,Nat.add_comm]

private theorem rowget (n k : ℕ) (xs : List Bool) (i j : ℕ) (hi : i<k) (hj : j<n) :
    (((RoundWire.readRows n k xs).1.getD i []).getD j false) = xs[i*n+j]?.getD false := by
  induction k generalizing xs i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => simp [RoundWire.readRows,List.getD_eq_getElem?_getD,List.getElem?_take,hj]
    | succ i =>
      have hi' : i<k := by omega
      simp only [RoundWire.readRows,List.getD_cons_succ,ih (xs.drop n) i hi']
      rw [List.getElem?_drop]
      congr 2
      rw [Nat.succ_mul]
      omega

private theorem body (n : ℕ) (data : List Bool) :
    let p := natRead (data.drop (n*n))
    view ((n,data.take (n*n)),parseRows (units p.2 p.1,tag n ++ p.2)) =
      RoundWire.decodeBody (n,data) := by
  simp only [RoundWire.decodeBody,remaining,←nat_all,parse_all,view,cols_entries]
  congr 2
  funext i j
  have h : i.val*n+j.val < n*n := by
    calc
      i.val*n+j.val < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by simp [Nat.succ_mul]
      _ ≤ n*n := Nat.mul_le_mul_right _ i.isLt
  rw [rowget n n data i.val j.val i.isLt j.isLt]
  simp [List.getElem?_take,h]

private theorem take_width (xs : List Bool) :
    xs.take (width xs + 1) = tag (width xs) ∨ xs.drop (width xs+1) = [] := by
  induction xs with
  | nil => simp [width]
  | cons b xs ih =>
    cases b
    · exact Or.inl (by simp [width,List.findIdx_cons,tag])
    · have h : width (true :: xs) = width xs+1 := by simp [width,List.findIdx_cons]
      rw [h]
      rcases ih with ih | ih
      · left
        change true :: xs.take (width xs+1) = _
        rw [ih]
        simp [tag,List.replicate_succ]
      · exact Or.inr ih

theorem view_raw (xs : List Bool) : view (raw xs) = RoundWire.decode xs := by
  let t := xs.drop (width xs+1)
  let n := width t
  let b := t.drop (n+1)
  simp only [RoundWire.decode,unary_all]
  change view ((n,b.take (n*n)),parseRows (units (natRead (b.drop (n*n))).2 (natRead (b.drop (n*n))).1,
    t.take (n+1) ++ (natRead (b.drop (n*n))).2)) = RoundWire.decodeBody (n,b)
  rcases take_width t with hh | hh
  · rw [show t.take (n+1)=tag n from hh,body]
  · have hb : b=[] := hh
    rw [hb]
    simpa [natRead,width,units,parseRows,parse] using body n []

end DualSepClusterLP.WireTM
end

/- WireGeometry -/
section
namespace DualSepClusterLP.WireGeometry
open WireTM
open OAI.MetricKMedian.InputParser OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly

def input (xs : List Bool) : List ℕ × Out :=
  let t := xs.drop (width xs+1)
  (List.range (t.take (width t)).length,raw xs)

@[fun_prop] theorem input_poly : Poly input := by
  unfold input
  apply pair
  · apply Poly.comp (f:=fun ys : List Bool => List.range ys.length) list_indices (g:=_) (by fun_prop)
  · exact raw_poly

theorem input_spec (xs : List Bool) : input xs = (List.range (raw xs).1.1, raw xs) := by
  unfold input raw
  have h (ys : List Bool) : width ys ≤ ys.length := List.findIdx_le_length
  simp only [List.length_take,Nat.min_eq_left (h _)]

def cellMass (rs : List Row) (i j : ℕ) : ℚ :=
  (rs.map (fun r => if r.1[i]?.getD false && r.1[j]?.getD false then r.2 else 0)).sum

@[fun_prop] theorem sum_comp {α : Type} [Coding α] {f : α → List ℚ} (h : Poly f) :
    Poly (fun a => (f a).sum) := Poly.comp (f:=List.sum) (g:=f) ⟨PolyProgram.ratSum⟩ h

@[fun_prop] theorem mass_comp {α : Type} [Coding α] [Inhabited α]
    {rs : α → List Row} {i j : α → ℕ} (hr : Poly rs) (hi : Poly i) (hj : Poly j) :
    Poly (fun a => cellMass (rs a) (i a) (j a)) := by
  unfold cellMass
  apply sum_comp
  apply list_map <;> fun_prop

def cell (x : Out) (i j : ℕ) : Bool × ℚ :=
  let k := if i≤j then i*x.1.1+j else j*x.1.1+i
  (x.1.2[k]?.getD false,cellMass x.2 i j)

def table (d : List ℕ × Out) : List (List (Bool × ℚ)) :=
  d.1.map (fun i => d.1.map (fun j => cell d.2 i j))

@[fun_prop] theorem table_poly : Poly table := by
  unfold table
  apply list_map
  · apply list_map
    · unfold cell
      fun_prop
    · fun_prop
  · fun_prop

noncomputable def machine : PolyProgram id enc (fun xs => table (input xs)) :=
  BooleanLists.packProgram.comp (Poly.comp table_poly input_poly).program

private theorem range_finRange (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  apply List.ext_getElem (by simp)
  intros
  simp only [List.getElem_range,List.getElem_map,List.getElem_finRange,Fin.val_cast]

private theorem mass_spec (x : Out) (i j : Fin x.1.1) :
    cellMass x.2 i.val j.val = SparsePivot.mass (WireTM.view x).2.2 i j := by
  unfold cellMass SparsePivot.mass WireTM.view
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro r _
  change _ = (if i ∈ Finset.univ.filter (fun a : Fin x.1.1 => r.1.getD a.val false) ∧
      j ∈ Finset.univ.filter (fun a : Fin x.1.1 => r.1.getD a.val false) then r.2 else 0)
  simp [List.getD_eq_getElem?_getD]

theorem cell_spec (x : Out) (i j : Fin x.1.1) :
    cell x i.val j.val = (unorderedSign (WireTM.view x).2.1 i j,
      SparsePivot.mass (WireTM.view x).2.2 i j) := by
  rw [cell,mass_spec]
  congr 1
  change _ = x.1.2[(min i j).val*x.1.1+(max i j).val]?.getD false
  by_cases h : i≤j
  · rw [min_eq_left h,max_eq_right h,if_pos (show i.val≤j.val from h)]
  · have h' := (le_of_not_ge h)
    rw [min_eq_right h',max_eq_left h',if_neg (show ¬i.val≤j.val from h)]

theorem table_spec (x : Out) : table (List.range x.1.1,x) =
    (List.finRange x.1.1).map (fun i => (List.finRange x.1.1).map (fun j =>
      (unorderedSign (WireTM.view x).2.1 i j,SparsePivot.mass (WireTM.view x).2.2 i j))) := by
  unfold table
  simp only [range_finRange,List.map_map,Function.comp_def,cell_spec]
  rfl

def ofDecoded (v : (n : ℕ) × (Graph n × SparseWeights n)) : List (List (Bool × ℚ)) :=
  (List.finRange v.1).map (fun i => (List.finRange v.1).map (fun j =>
    (unorderedSign v.2.1 i j, SparsePivot.mass v.2.2 i j)))

theorem table_input (xs : List Bool) : table (input xs) = ofDecoded (RoundWire.decode xs) := by
  rw [input_spec,table_spec,←view_raw]
  rfl

def columns (d : List ℕ × Out) : List Row :=
  d.2.2.map (fun r => (d.1.map (fun i => r.1[i]?.getD false),r.2))

@[fun_prop] theorem columns_poly : Poly columns := by
  unfold columns
  apply list_map <;> fun_prop

theorem columns_spec (x : Out) : columns (List.range x.1.1,x) = (WireTM.view x).2.2.map WireTM.rowOf := by
  simp only [columns,WireTM.view,range_finRange,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro r _
  change ((List.finRange x.1.1).map (fun i => r.1[i.val]?.getD false),r.2) =
    ((List.finRange x.1.1).map (fun i => decide (i ∈ Finset.univ.filter
      (fun j : Fin x.1.1 => r.1.getD j.val false))),r.2)
  simp [List.getD_eq_getElem?_getD]

theorem columns_input (xs : List Bool) : columns (input xs) = (RoundWire.decode xs).2.2.map WireTM.rowOf := by
  rw [input_spec,columns_spec,view_raw]

end DualSepClusterLP.WireGeometry
end

/- ClockMachine -/
section
namespace DualSepClusterLP.ClockMachine
open OAI.MetricKMedian.Binary
open WordRound (Word raw mask)
open PivotMachines (RP literal plus minus times quotient)
noncomputable section

/-- Each edge record stores the two indices, sign and sparse co-membership mass. -/
abbrev Edge := (ℕ × ℕ) × (Bool × ℚ)
abbrev eIndex := encodePair Nat.bits Nat.bits
abbrev eValue := encodePair encodeBool Ratio.encode
abbrev eEdge := encodePair eIndex eValue
abbrev Ctx := List Edge × List Word
abbrev eCtx := encodePair (encodeList eEdge) (encodeList raw)
abbrev masksEnc := encodePair raw raw

def budget {α : Type} {e : α → Word} {s : α → Bool} {y : α → ℚ}
    (hs : PolyProgram e encodeBool s) (hy : RP e y) : RP e (fun a => SparseClock.budget (s a) (y a)) := by
  let numerator := times (literal e 2) (minus (literal e 1) hy)
  let den := minus (literal e 2) hy
  exact (quotient (PolyProgram.ite hs hy numerator) den).congr _ (fun a => by
    cases h : s a <;> simp [SparseClock.budget,h])

def atBit {α : Type} {ea : α → Word} {f : α → Word} {j : α → ℕ}
    (p : PolyProgram ea raw f) (q : PolyProgram ea Nat.bits j) :
    PolyProgram ea encodeBool (fun a => (f a).getD (j a) false) := by
  exact (((p.comp BooleanLists.packProgram).fanout q).comp (PolyProgram.listGetD encodeBool false)).congr _
    (fun _ => (List.getD_eq_getElem?_getD ..).symm)

def contribution (wk : Word × Word) (e : Edge) : ℚ :=
  let (i,j) := e.1
  let (p,y) := e.2
  let a := wk.2.getD i false
  let b := wk.2.getD j false
  if i<j ∧ wk.1.getD i false ∧ wk.1.getD j false then
    (if a || b then SparseClock.budget p y else 0) -
      (if (if p then xor a b else a && b) then 1 else 0)
  else 0

def edgeProgram : PolyProgram (encodePair masksEnc eEdge) Ratio.encode
    (fun a => contribution a.1 a.2) := by
  open PolyProgram in
  let wK := fst masksEnc eEdge
  let e := snd masksEnc eEdge
  let w := wK.comp (fst raw raw)
  let k := wK.comp (snd raw raw)
  let ij := e.comp (fst eIndex eValue)
  let py := e.comp (snd eIndex eValue)
  let i := ij.comp (fst Nat.bits Nat.bits)
  let j := ij.comp (snd Nat.bits Nat.bits)
  let sign := py.comp (fst encodeBool Ratio.encode)
  let y := py.comp (snd encodeBool Ratio.encode)
  let wi := atBit w i
  let wj := atBit w j
  let a := atBit k i
  let b := atBit k j
  let lt := ((j.fanout i).comp natLE).comp boolNot
  let live := (lt.fanout ((wi.fanout wj).comp boolAnd)).comp boolAnd
  let bits := a.fanout b
  let made := bits.comp boolOr
  let cost := ite sign (bits.comp boolAnd) (bits.comp boolXor)
  let zero := literal (encodePair masksEnc eEdge) 0
  let gain := minus (ite made zero (budget sign y)) (ite cost zero (literal _ 1))
  exact (ite live zero gain).congr _ (fun a => by
    simp only [contribution,Function.comp_apply,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,
      not_le])

def margin (edges : List Edge) (w k : Word) : ℚ :=
  (edges.map (contribution (w,k))).sum

def accepts (ctx : List Edge × Word) (k : Word) : Bool :=
  (WordRound.zip (fun p => p.1 && p.2) ctx.2 k).any id && decide (0 ≤ margin ctx.1 ctx.2 k)

abbrev eState := encodePair (encodeList eEdge) raw

def acceptProgram : PolyProgram (encodePair eState raw) encodeBool (fun t => accepts t.1 t.2) := by
  open PolyProgram in
  let state := fst eState raw
  let edges := state.comp (fst (encodeList eEdge) raw)
  let w := state.comp (snd (encodeList eEdge) raw)
  let k := snd eState raw
  let wk := w.fanout k
  let sum := ((wk.fanout edges).comp (edgeProgram.listMapWith default 0)).comp ratSum
  let ok := ((literal _ 0).fanout sum).comp ratLE
  let inter := wk.comp (WordRound.zipProgram (fun p => p.1 && p.2))
  let nonempty := (inter.comp BooleanLists.packProgram).comp ((identity encodeBool).listAny false)
  exact ((nonempty.fanout ok).comp boolAnd).congr _ (fun _ => rfl)

def select (input : Ctx × Word) : Word :=
  let (ctx,w) := input
  let ok := ctx.2.filter (accepts (ctx.1,w))
  ok.head?.getD (w.map (fun _ => false))

def selector : PolyProgram (encodePair eCtx raw) raw select := by
  open PolyProgram in
  let inp := fst eCtx raw
  let w := snd eCtx raw
  let es := inp.comp (fst _ _)
  let cols := inp.comp (snd _ _)
  let hits := ((es.fanout w).fanout cols).comp (acceptProgram.listFilterWith [] default)
  let none := hits.comp (listIsEmpty raw)
  let k := hits.comp (listHead raw [])
  let zero := ((w.comp BooleanLists.packProgram).comp ((constant encodeBool encodeBool false).listMap false)).comp
    BooleanLists.unpackProgram
  exact (ite none k zero).congr _ (fun t => by
    rcases t with ⟨⟨es,cols⟩,w⟩
    let hits := cols.filter (accepts (es,w))
    change (if hits.isEmpty then w.map (fun _ => false) else hits.head?.getD []) =
      hits.head?.getD (w.map (fun _ => false))
    cases hits <;> rfl)

end
end DualSepClusterLP.ClockMachine
end

/- ClockMachineSpec -/
section
namespace DualSepClusterLP.ClockMachine
open WordRound (mask Word)
def edgeOf {n : ℕ} (G : Graph n) (L : SparseWeights n) (i j : Fin n) : Edge :=
  ((i.val,j.val),unorderedSign G i j,SparsePivot.mass L i j)

def table {n : ℕ} (G : Graph n) (L : SparseWeights n) : Ctx :=
  ((List.finRange n).flatMap (fun i => (List.finRange n).map (edgeOf G L i)),
    (L.map Prod.fst).map mask)

private theorem mask_get {n : ℕ} (W : Finset (Fin n)) (i : Fin n) :
    (mask W).getD i.val false = decide (i ∈ W) := by
  simp [mask,← List.ofFn_eq_map,List.getD_eq_getElem?_getD]

private theorem contribution_eq {n : ℕ} (G : Graph n) (L : SparseWeights n) (W S : Finset (Fin n)) (i j : Fin n) :
    contribution (mask W,mask S) (edgeOf G L i j) =
      (if i∈W then if j∈W then if i<j then SparseClock.pairGain G L S i j else 0 else 0 else 0) := by
  simp only [contribution,edgeOf,mask_get]
  by_cases ht : i < j
  · have hu : unorderedSign G i j = G i j := by simp [unorderedSign,min_eq_left ht.le,max_eq_right ht.le]
    rw [hu]
    by_cases hi : i ∈ W <;> by_cases hj : j ∈ W <;> by_cases hij : i<j <;>
      by_cases ha : i ∈ S <;> by_cases hb : j ∈ S <;> cases hs : G i j <;>
      simp [SparseClock.pairGain,hi,hj,hij,ha,hb,hs]
  · have htval : ¬i.val < j.val := ht
    simp [ht,htval]

private theorem sum_flat {α : Type} (xs : List α) (f : α → List ℚ) :
    (xs.flatMap f).sum = (xs.map (fun i => (f i).sum)).sum := by
  induction xs <;> simp_all

theorem margin_table {n : ℕ} (G : Graph n) (L : SparseWeights n) (W S : Finset (Fin n)) :
    margin (table G L).1 (mask W) (mask S) = SparseClock.margin G L W S := by
  simp only [margin,table,List.map_flatMap,List.map_map,Function.comp_def,sum_flat]
  simp only [contribution_eq,←List.ofFn_eq_map,List.sum_ofFn,SparseClock.margin]
  simp [Finset.sum_ite_irrel]

private theorem meets {n : ℕ} (W S : Finset (Fin n)) :
    (WordRound.zip (fun p => p.1 && p.2) (mask W) (mask S)).any id =
      decide ((W ∩ S).Nonempty) := by
  rw [mask,mask,WordRound.zip_maps]
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true,Finset.Nonempty,Finset.mem_inter]

theorem select_table {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n)) :
    select (table G L,mask W) = mask (SparseClock.step G L W) := by
  let ok (S : Finset (Fin n)) := decide ((W ∩ S).Nonempty ∧ 0 ≤ SparseClock.margin G L W S)
  have hak (S : Finset (Fin n)) : accepts ((table G L).1,mask W) (mask S) = ok S := by
    simp [accepts,ok,meets,margin_table]
  have hz : (mask W).map (fun _ => false) = mask (∅ : Finset (Fin n)) := by simp [mask,Function.comp_def]
  let es := (table G L).1
  change (((L.map Prod.fst).map mask).filter (accepts (es,mask W))).head?.getD ((mask W).map (fun _ => false)) =
    mask (((L.map Prod.fst).find? ok).getD ∅)
  rw [hz]
  generalize (L.map Prod.fst) = xs
  induction xs with
  | nil => rfl
  | cons S xs ih =>
    have h : accepts (es,mask W) (mask S) = ok S := hak S
    cases hb : ok S <;> simp only [List.map_cons,List.filter_cons,List.find?_cons,h,hb,
      Bool.false_eq_true,if_false,if_true,Option.getD_some,List.head?_cons]
    exact ih

end DualSepClusterLP.ClockMachine
end

/- RoundContext -/
section
namespace DualSepClusterLP.RoundContext
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
open WordRound (Word raw mask)
abbrev Matrix := List (List (Bool × ℚ))
abbrev Data := (List ℕ × Word) × (Matrix × List Word)

def canonical {n : ℕ} (G : Graph n) (L : SparseWeights n) : Data :=
  ((List.range n,matrixBits G),
    (WireGeometry.ofDecoded ⟨n,G,L⟩,(L.map Prod.fst).map mask))

def prepare (d : List ℕ × WireTM.Out) : Data :=
  let x := d.2
  let graph := d.1.flatMap (fun i => d.1.map (fun j => x.1.2[i*x.1.1+j]?.getD false))
  let masks := x.2.map (fun e => d.1.map (fun i => e.1[i]?.getD false))
  ((d.1,graph),WireGeometry.table d,masks)

@[fun_prop] theorem prepare_poly : Poly prepare := by
  unfold prepare
  apply pair
  · apply pair
    · fun_prop
    · apply list_flatMap
      · apply list_map <;> fun_prop
      · fun_prop
  · apply pair
    · exact WireGeometry.table_poly
    · apply list_map
      · apply list_map <;> fun_prop
      · fun_prop

private theorem range_fin (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

theorem prepare_spec (x : WireTM.Out) :
    prepare (List.range x.1.1,x) = canonical (WireTM.view x).2.1 (WireTM.view x).2.2 := by
  have hm' : x.2.map (fun r => (List.range x.1.1).map (fun i => r.1[i]?.getD false)) =
      (((WireTM.view x).2.2).map Prod.fst).map mask := by
    have h := congrArg (fun rs : List WireTM.Row => rs.map Prod.fst) (WireGeometry.columns_spec x)
    simpa only [WireGeometry.columns,List.map_map,Function.comp_def,WireTM.rowOf,mask] using h
  have hg : (List.range x.1.1).flatMap (fun i => (List.range x.1.1).map (fun j =>
      x.1.2[i*x.1.1+j]?.getD false)) = matrixBits (WireTM.view x).2.1 := by
    rw [range_fin]
    simp only [List.flatMap_map,List.map_map,Function.comp_def,matrixBits,WireTM.view]
  simp only [prepare,hg,hm',canonical,WireGeometry.table_spec,WireGeometry.ofDecoded,WireTM.view]

def clockData (d : Data) : ClockMachine.Ctx :=
  (d.1.1.flatMap (fun i => d.1.1.map (fun j =>
      ((i,j),((d.2.1[i]?.getD [])[j]?.getD (false,0))))),d.2.2)

@[fun_prop] theorem clockData_poly : Poly clockData := by
  unfold clockData; apply pair
  · apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
  · fun_prop

private theorem nth_map {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    ((List.finRange n).map f)[i.val]?.getD d = f i := by
  simp [←List.ofFn_eq_map]

theorem clockData_spec {n : ℕ} (G : Graph n) (L : SparseWeights n) :
    clockData (canonical G L) = ClockMachine.table G L := by
  simp only [clockData,canonical,WireGeometry.ofDecoded,range_fin,List.flatMap_map,
    List.map_map,Function.comp_def,nth_map,ClockMachine.table]
  rfl

abbrev qword := encodeList encodeBool

/-- Convert the list-of-bits encoding of column masks to raw binary-word fields. -/
noncomputable def clockProgram : PolyProgram (encodePair (enc (α:=Data)) raw) raw
    (fun t => ClockMachine.select (clockData t.1,t.2)) := by
  open PolyProgram in
  let edges := fst (encodeList ClockMachine.eEdge) (encodeList qword)
  let masks := (snd (encodeList ClockMachine.eEdge) (encodeList qword)).comp
    (BooleanLists.unpackProgram.listMap [])
  let src := (fst (enc (α:=Data)) raw).comp clockData_poly.program
  let clk := src.comp (edges.fanout masks)
  exact ((clk.fanout (snd (enc (α:=Data)) raw)).comp ClockMachine.selector).congr _ (fun t => by
    simp only [Function.comp_def,List.map_id_fun,id_eq])

def start (xs : Word) : Data × Word :=
  let d := prepare (WireGeometry.input xs)
  (d,d.1.1.map (fun _ => true))

noncomputable def startProgram : PolyProgram raw (encodePair (enc (α:=Data)) raw) start := by
  let init : Poly (fun x : Data => x.1.1.map (fun _ => true)) := by apply list_map <;> fun_prop
  let cp := BooleanLists.packProgram.comp (Poly.comp prepare_poly WireGeometry.input_poly).program
  exact (cp.fanout ((cp.comp init.program).comp BooleanLists.unpackProgram)).congr _ (fun _ => rfl)

noncomputable def graphProgram : PolyProgram (enc (α:=Data)) raw (fun x : Data => x.1.2) := by
  let p : Poly (fun x : Data => x.1.2) := by fun_prop
  exact p.program.comp BooleanLists.unpackProgram

def initialDecoded (v : (n : ℕ) × (Graph n × SparseWeights n)) : Data × Word :=
  (canonical v.2.1 v.2.2,mask (Finset.univ : Finset (Fin v.1)))

theorem start_spec (xs : Word) : start xs = initialDecoded (RoundWire.decode xs) := by
  rw [←WireTM.view_raw]
  simp only [start,WireGeometry.input_spec,prepare_spec,initialDecoded,canonical,mask,
    List.map_const',List.length_range,List.length_finRange,Finset.mem_univ,decide_true]

end DualSepClusterLP.RoundContext
end

/- GainStock -/
section
namespace DualSepClusterLP.DenseGain
open OAI.MetricKMedian.Binary

/-- Convert the machine library's polynomial clocks into the monomial format used
by the mission. The extra one in the input length handles the empty input. -/
theorem polynomialClock (p : Polynomial ℕ) :
    ∃ A b : ℕ, ∀ m : ℕ, p.eval m ≤ A*(m+1)^b := by
  induction p using Polynomial.induction_on' with
  | monomial k a =>
    exact ⟨a,k,fun m => by simp only [Polynomial.eval_monomial]; gcongr; omega⟩
  | add p q hp hq =>
    obtain ⟨A,b,hA⟩ := hp
    obtain ⟨C,d,hC⟩ := hq
    refine ⟨A+C,b+d,fun m => ?_⟩
    rw [Polynomial.eval_add,add_mul]
    refine (Nat.add_le_add (hA m) (hC m)).trans (Nat.add_le_add ?_ ?_)
    · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))


end DualSepClusterLP.DenseGain
end

/- StockRounder -/
section
namespace DualSepClusterLP.RoundContext
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
open WordRound (Word raw mask)

def choosePivot (t : Data × Word) : Word :=
  PivotSelect.select FixMachine.cluster (t.1.2,t.2)

theorem pivot_eq {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n)) :
    choosePivot (canonical G L,mask W) = mask (SparsePivot.step G L W) := by
  have hc (u : Fin n) (S : Finset (Fin n)) := FixMachine.cluster_correct G L W S u
  have he := PivotSelect.select_exact G L W FixMachine.cluster hc
  simpa only [choosePivot,canonical,PivotSelect.environment,List.map_map,Function.comp_def,
    PivotSelect.matrixOf,WireGeometry.ofDecoded] using he

noncomputable def pivotProgram : PolyProgram (encodePair (enc (α:=Data)) raw) raw choosePivot := by
  let p : Poly choosePivot := by
    unfold choosePivot
    exact Poly.comp (PivotSelect.select_poly FixMachine.poly_cluster) (by fun_prop)
  let wr := ((PolyProgram.fst (enc (α:=Data)) raw).fanout
    ((PolyProgram.snd (enc (α:=Data)) raw).comp BooleanLists.packProgram))
  exact ((wr.comp p.program).comp BooleanLists.unpackProgram).congr _ (fun _ => rfl)

def answer (t : Data × Word) : Word :=
  WordRound.cheaper (WordRound.upper t.2) t.1.1.2
    (WordRound.totalRun (fun a => ClockMachine.select (clockData a.1,a.2)) t)
    (WordRound.totalRun choosePivot t)

noncomputable def answerProgram : PolyProgram (encodePair (enc (α:=Data)) raw) raw answer :=
  WordRound.totalTwoRoundsProgram graphProgram clockProgram pivotProgram

theorem answer_correct {n : ℕ} (G : Graph n) (L : SparseWeights n) :
    answer (canonical G L,mask (Finset.univ : Finset (Fin n))) =
      partitionOutput (if disagreements G (RoundFold.run (SparseClock.step G L)) ≤
        disagreements G (RoundFold.run (SparsePivot.step G L))
        then RoundFold.run (SparseClock.step G L) else RoundFold.run (SparsePivot.step G L)) := by
  apply WordRound.totalTwoRounds_spec
  · intro W
    simp only [clockData_spec,ClockMachine.select_table]
  · exact pivot_eq G L

private theorem final_eq (v : (n : ℕ) × (Graph n × SparseWeights n)) :
    answer (initialDecoded v) = (let ⟨_,G,L⟩ := v
      let C := RoundFold.run (SparseClock.step G L)
      let P := RoundFold.run (SparsePivot.step G L)
      partitionOutput (if disagreements G C ≤ disagreements G P then C else P)) := by
  rcases v with ⟨n,G,L⟩
  exact answer_correct G L

noncomputable def program : PolyProgram raw raw RoundWire.output :=
  (startProgram.comp answerProgram).congr _ (fun xs => by
    change answer (start xs) = RoundWire.output xs
    rw [start_spec]
    exact final_eq _)

end DualSepClusterLP.RoundContext

open DualSepClusterLP

theorem solution :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧ ∀ (w : List Bool),
        Nonempty (Turing.TM2OutputsInTime M.tm (w.map M.inputAlphabet.symm)
          (some ((RoundWire.output w).map M.outputAlphabet.symm)) (A * (w.length + 1)^b)) := by
  let p := RoundContext.program
  obtain ⟨A,b,h⟩ := DenseGain.polynomialClock p.time
  refine ⟨p.stock.toTM2ComputableAux,A,b,p.finite_work,?_⟩
  intro w
  have hr := p.stock.outputsFun w
  exact ⟨⟨hr.toEvalsTo,hr.steps_le_m.trans (h _)⟩⟩
end
